use super::primitive::{endoscale_pair, endoscale_scalar, i2lebsp};
use super::{EndoscaleInstructions, EndoscaleLookup};
use group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    Curve,
};
use halo2_gadgets::{
    ecc::chip::{add_incomplete, witness_point, NonIdentityEccPoint},
    utilities::{
        bool_check,
        boolean::Bit,
        decompose_running_sum::{RunningSumConfig, Window},
        transpose_option_vec, UtilitiesInstructions,
    },
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector, TableColumn},
    poly::Rotation,
};
use pasta_curves::arithmetic::{CurveAffine, FieldExt};
use std::{convert::TryInto, marker::PhantomData};

/// A K-bit word.
#[derive(Debug, Clone)]
pub struct Word<F: FieldExt, const K: usize>(AssignedCell<Window<K>, F>);

/// An endoscalar representing a K-bit word.
#[derive(Debug)]
pub struct Endoscalar<F: FieldExt>(AssignedCell<F, F>);

/// Configuration for endoscalar table.
#[derive(Copy, Clone, Debug)]
pub struct TableConfig<F: FieldExt, const K: usize> {
    pub(in crate::recursion) bits: TableColumn,
    pub(in crate::recursion) endoscalar: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const K: usize> TableConfig<F, K> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        TableConfig {
            bits: meta.lookup_table_column(),
            endoscalar: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "endoscalar_map",
            |mut table| {
                for index in 0..(1 << K) {
                    table.assign_cell(|| "bits", self.bits, index, || Ok(F::from(index as u64)))?;
                    table.assign_cell(
                        || "endoscalar",
                        self.endoscalar,
                        index,
                        || Ok(endoscale_scalar::<F, K>(i2lebsp(index as u64))),
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// Columns used in processing endoscalars.
#[derive(Clone, Debug)]
pub struct EndoscaleConfig<C: CurveAffine, const K: usize>
where
    C::Base: PrimeFieldBits,
{
    // Selector enabling the lookup.
    q_lookup: Selector,
    // Selector enabling endoscaling commitment.
    q_commit: Selector,
    // Public inputs are provided as endoscalars. Each endoscalar corresponds
    // to a K-bit chunk.
    endoscalars: Column<Instance>,
    // An additional advice column where endoscalar values are copied and used
    // in the lookup argument.
    endoscalars_copy: Column<Advice>,
    // The K-bit chunk representations of the public inputs.
    // These are used in-circuit for scalar multiplication.
    word: Column<Advice>,
    // Accumulator used in committing to a word by the endoscaling algorithm.
    // (x, y) coordinates
    acc: (Column<Advice>, Column<Advice>),
    // Point that is added to the accumulator.
    point: (Column<Advice>, Column<Advice>),
    // Fixed that is used in endoscaling.
    base: (Column<Advice>, Column<Advice>),
    // Bits used in endoscaling. These are in (b_0, b_1) pairs.
    bits: (Column<Advice>, Column<Advice>),
    // Table mapping words to their corresponding endoscalars.
    pub(in crate::recursion) table: TableConfig<C::Base, K>,
    // Configuration used for boolean decomposition of field elements to be used
    // in endoscaling.
    // Each field element is assumed to encode a multiple of `K` bits.
    // Each `K`-bit word is mapped to an endoscalar.
    decomposition: RunningSumConfig<C::Base, 2>,
    // Config used in adding to the accumulator.
    add_config: add_incomplete::Config<C>,
    // Config used in witnessing accumulator points.
    acc_point_config: witness_point::Config<C>,
    // Config used in witnessing endoscaled points.
    endo_point_config: witness_point::Config<C>,
}

impl<C: CurveAffine, const K: usize> UtilitiesInstructions<C::Base> for EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    type Var = AssignedCell<C::Base, C::Base>;
}

impl<C: CurveAffine, const K: usize> EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    #[allow(dead_code)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        endoscalars: Column<Instance>,
        endoscalars_copy: Column<Advice>,
        word: Column<Advice>,
        acc: (Column<Advice>, Column<Advice>),
        point: (Column<Advice>, Column<Advice>),
        base: (Column<Advice>, Column<Advice>),
        bits: (Column<Advice>, Column<Advice>),
        table: TableConfig<C::Base, K>,
    ) -> Self {
        let decomposition = {
            let q_range_check = meta.selector();
            // TODO: Pass this advice column in.
            let z = meta.advice_column();
            RunningSumConfig::configure(meta, q_range_check, z)
        };
        let add_config = add_incomplete::Config::configure(meta, point.0, point.1, acc.0, acc.1);
        let acc_point_config = witness_point::Config::configure(meta, acc.0, acc.1);
        let endo_point_config = witness_point::Config::configure(meta, point.0, point.1);
        let config = Self {
            q_lookup: meta.complex_selector(),
            q_commit: meta.complex_selector(),
            endoscalars,
            endoscalars_copy,
            word,
            acc,
            point,
            base,
            bits,
            table,
            decomposition,
            add_config,
            acc_point_config,
            endo_point_config,
        };

        meta.enable_equality(config.endoscalars);
        meta.enable_equality(config.endoscalars_copy);
        meta.enable_equality(base.0);
        meta.enable_equality(base.1);

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let word = meta.query_advice(config.word, Rotation::cur());
            let endoscalars = meta.query_advice(config.endoscalars_copy, Rotation::cur());

            // Endoscalar that maps to the K-string of 0's.
            let default = { Expression::<C::Base>::Constant(endoscale_scalar([false; K])) };
            let not_q_lookup = Expression::Constant(C::Base::one()) - q_lookup.clone();

            vec![
                (q_lookup.clone() * word, table.bits),
                (
                    q_lookup * endoscalars + not_q_lookup * default,
                    table.endoscalar,
                ),
            ]
        });

        /*
            The accumulator is initialised to [2](φ(P) + P) = (init_x, init_y).

            | b_0 | b_1 |   endo_x  |   endo_y   | acc_x  | acc_y  | P_x | P_y | <- column names
            --------------------------------------------------------------------
            | b_0 | b_1 | endo(P)_x |  endo(P)_y | init_x | init_y | P_x | P_y |

            (0, 0) -> (P_x, -P_y)
            (0, 1) -> (ζ * P_x, -P_y)
            (1, 0) -> (P_x, P_y)
            (1, 1) -> (ζ * P_x, P_y)
        */
        meta.create_gate("Endoscaling", |meta| {
            let q_commit = meta.query_selector(config.q_commit);

            // Pair of bits from the decomposition.
            let b_0 = meta.query_advice(config.bits.0, Rotation::cur());
            let b_1 = meta.query_advice(config.bits.1, Rotation::cur());

            // Boolean-constrain b_0, b_1
            let b_0_check = bool_check(b_0.clone());
            let b_1_check = bool_check(b_1.clone());

            // Check that `b_0, b_1` are consistent with the running sum decomposition.
            let decomposition_check = {
                let word = b_0.clone() + Expression::Constant(C::Base::from(2)) * b_1.clone();
                let expected_word = {
                    let z_cur = meta.query_advice(config.decomposition.z(), Rotation::cur());
                    let z_next = meta.query_advice(config.decomposition.z(), Rotation::next());
                    //    z_i = 2^{K}⋅z_{i + 1} + k_i
                    // => k_i = z_i - 2^{K}⋅z_{i + 1}
                    z_cur - z_next * C::Base::from(1 << 2)
                };

                word - expected_word
            };

            // If the first bit is set, check that endo_y = -P_y
            let y_check = {
                let endo_y = meta.query_advice(config.point.1, Rotation::cur());
                let p_y = meta.query_advice(config.base.1, Rotation::cur());
                b_0 * (endo_y + p_y)
            };
            // If the second bit is set, check that endo_x = ζ * P_x
            let x_check = {
                let endo_x = meta.query_advice(config.point.0, Rotation::cur());
                let p_x = meta.query_advice(config.base.0, Rotation::cur());
                let zeta = Expression::Constant(C::Base::ZETA);
                b_1 * (endo_x - zeta * p_x)
            };

            std::array::IntoIter::new([
                ("b_0_check", b_0_check),
                ("b_1_check", b_1_check),
                ("decomposition_check", decomposition_check),
                ("x_check", x_check),
                ("y_check", y_check),
            ])
            .map(move |(name, poly)| (name, q_commit.clone() * poly))
        });

        config
    }
}

impl<C: CurveAffine, const K: usize, const N: usize> EndoscaleInstructions<C, K, N>
    for EndoscaleConfig<C, K>
where
    C::Base: EndoscaleLookup<K, N> + PrimeFieldBits,
{
    type Word = Word<C::Base, K>;
    type Commitment = NonIdentityEccPoint<C>;

    fn load_endoscale_scalar_table(
        &self,
        layouter: &mut impl Layouter<C::Base>,
    ) -> Result<(), Error> {
        self.table.load(layouter)
    }

    fn get_bitstring(
        &self,
        mut layouter: impl Layouter<C::Base>,
        row: usize,
    ) -> Result<Self::Word, Error> {
        layouter.assign_region(
            || "get_bitstring",
            |mut region| {
                // Enable lookup
                self.q_lookup.enable(&mut region, 0)?;

                // Copy endoscalar in from instance column
                let scalar = region
                    .assign_advice_from_instance(
                        || "copy endoscalar",
                        self.endoscalars,
                        row,
                        self.endoscalars_copy,
                        0,
                    )
                    .map(Endoscalar)?;

                let bitstring = scalar
                    .0
                    .value()
                    .map(|scalar| {
                        // Look up the bitstring corresponding to the endoscalar
                        C::Base::table()
                            .iter()
                            .find(|(_, table_scalar)| scalar == table_scalar)
                            .expect("should have found scalar")
                            .0
                    })
                    .map(Window::new);

                // Witness bitstring
                let word = {
                    region
                        .assign_advice(
                            || format!("row {}", row),
                            self.word,
                            0,
                            || bitstring.ok_or(Error::Synthesis),
                        )
                        .map(Word)?
                };

                Ok(word)
            },
        )
    }

    fn endoscale_base_fixed(
        &self,
        mut layouter: impl Layouter<C::Base>,
        base: C,
        word: &Self::Word,
        prev_acc: Option<Self::Commitment>,
    ) -> Result<Self::Commitment, Error> {
        layouter.assign_region(
            || "Commit word",
            |mut region| {
                // Initialise accumulator.
                let (acc, offset) = self.init_acc(&mut region, 0, base, prev_acc.clone())?;

                // Decompose the word into 2-bit windows.
                self.decomposition.witness_decompose::<K>(
                    &mut region,
                    offset,
                    word.0.value_field().map(|v| v.evaluate()),
                    true,
                    K / 2,
                )?;

                let pairs = {
                    let pairs = word.0.value().map(|word| pairs(word.bits()));
                    transpose_option_vec(pairs, K / 2)
                };

                let (acc, _) = self.commit_inner(&mut region, offset, base, pairs.to_vec(), acc)?;

                Ok(acc)
            },
        )
    }

    fn endoscale_base_var<L: Layouter<C::Base>, const NUM_BITS: usize>(
        &self,
        mut layouter: L,
        bases: Vec<C>,
        field_elem: AssignedCell<C::Base, C::Base>,
        prev_acc: Option<Self::Commitment>,
    ) -> Result<Self::Commitment, Error> {
        assert_eq!(NUM_BITS % K, 0);
        // The field element must be able to contain NUM_BITS bits.
        assert!(C::Base::NUM_BITS as usize >= NUM_BITS);
        // There must be one base per word.
        let num_words = NUM_BITS / K;
        assert!(bases.len() >= num_words);

        layouter.assign_region(
            || "Commit to field element",
            |mut region| {
                // Initialise accumulator.
                let (mut acc, offset) =
                    self.init_acc(&mut region, 0, bases[0], prev_acc.clone())?;

                // Decompose the field element into 2-bit windows.
                self.decomposition.copy_decompose::<NUM_BITS>(
                    &mut region,
                    offset,
                    &field_elem,
                    true,
                    NUM_BITS / 2,
                )?;

                let pairs = {
                    let bits = field_elem.value_field().map(|v| {
                        v.evaluate()
                            .to_le_bits()
                            .iter()
                            .by_val()
                            .take(NUM_BITS)
                            .collect::<Vec<_>>()
                    });
                    let pairs = bits.map(|bits| pairs::<NUM_BITS>(bits.try_into().unwrap()));
                    transpose_option_vec(pairs, NUM_BITS / 2)
                };

                let mut offset = offset;

                // For every K / 2 pairs, use a new base.
                for word_idx in 0..num_words {
                    let pairs = &pairs[word_idx * (K / 2)..(word_idx * (K / 2) + K / 2)];
                    let (new_acc, new_offset) = self.commit_inner(
                        &mut region,
                        offset,
                        bases[word_idx],
                        pairs.to_vec(),
                        acc,
                    )?;
                    offset = new_offset;
                    acc = new_acc;
                }

                Ok(acc)
            },
        )
    }
}

impl<C: CurveAffine, const K: usize> EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    fn init_acc(
        &self,
        region: &mut Region<'_, C::Base>,
        mut offset: usize,
        base: C,
        prev_acc: Option<NonIdentityEccPoint<C>>,
    ) -> Result<(NonIdentityEccPoint<C>, usize), Error> {
        // The accumulator is initialised to [2](φ(P) + P) = (init_x, init_y).
        let mut acc = {
            let acc = base.to_curve() + base * C::Scalar::ZETA;
            self.acc_point_config
                .point_non_id(Some(acc.to_affine()), offset, region)?
        };

        // If there was a previous accumulator, add it to the current one.
        if let Some(prev_acc) = &prev_acc {
            acc = self
                .add_config
                .assign_region(&prev_acc, &acc, offset, region)?;

            offset += 1;
        }

        Ok((acc, offset))
    }

    fn commit_inner(
        &self,
        region: &mut Region<'_, C::Base>,
        mut offset: usize,
        base: C,
        pairs: Vec<Option<(bool, bool)>>,
        mut acc: NonIdentityEccPoint<C>,
    ) -> Result<(NonIdentityEccPoint<C>, usize), Error> {
        for (pair_idx, pair) in pairs.into_iter().enumerate() {
            self.q_commit.enable(region, offset)?;

            // Assign base_x
            region.assign_advice_from_constant(
                || "base_x",
                self.base.0,
                offset,
                *base.coordinates().unwrap().x(),
            )?;

            // Assign base_y
            region.assign_advice_from_constant(
                || "base_y",
                self.base.1,
                offset,
                *base.coordinates().unwrap().y(),
            )?;

            // Assign b_0
            let b_0: Option<Bit> = pair.map(|(b_0, _)| b_0.into());
            region.assign_advice(
                || format!("pair_idx: {}, b_0", pair_idx),
                self.bits.0,
                offset,
                || b_0.ok_or(Error::Synthesis),
            )?;

            // Assign b_1
            let b_1: Option<Bit> = pair.map(|(_, b_1)| b_1.into());
            region.assign_advice(
                || format!("pair_idx: {}, b_1", pair_idx),
                self.bits.1,
                offset,
                || b_1.ok_or(Error::Synthesis),
            )?;

            // Assign endoscaled point
            let endo = pair.map(|pair| endoscale_pair::<C>(pair, base).unwrap());
            let endo = self.endo_point_config.point_non_id(endo, offset, region)?;

            // Add endo to acc.
            acc = self.add_config.assign_region(&endo, &acc, offset, region)?;

            offset += 1;
        }

        Ok((acc, offset))
    }
}

/// Helper to break a string of bits into pairs of bits.
fn pairs<const K: usize>(bits: [bool; K]) -> Vec<(bool, bool)> {
    let mut pairs: Vec<(bool, bool)> = Vec::new();
    for pair_idx in 0..(K / 2) {
        pairs.push((bits[pair_idx * 2], bits[pair_idx * 2 + 1]));
    }
    pairs
}

#[cfg(test)]
mod tests {
    use super::{EndoscaleConfig, EndoscaleInstructions, EndoscaleLookup, TableConfig, Word};
    use crate::recursion::endoscale::primitive;
    use halo2_gadgets::utilities::UtilitiesInstructions;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Circuit, ConstraintSystem, Error},
        poly::commitment::Params,
    };
    use pasta_curves::{arithmetic::FieldExt, pallas, vesta};

    use std::marker::PhantomData;

    impl EndoscaleLookup<10, 1024> for pallas::Base {
        fn table() -> [([bool; 10], Self); 1024] {
            primitive::fp::TABLE
        }
    }

    impl EndoscaleLookup<10, 1024> for vesta::Base {
        fn table() -> [([bool; 10], Self); 1024] {
            primitive::fq::TABLE
        }
    }

    #[derive(Default)]
    struct MyCircuit<F: FieldExt>(PhantomData<F>);

    impl Circuit<pallas::Base> for MyCircuit<pallas::Base> {
        type Config = EndoscaleConfig<pallas::Affine, 10>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
            let table_config = TableConfig::configure(meta);

            let _ = meta.instance_column();
            let constants = meta.fixed_column();
            meta.enable_constant(constants);
            let endoscalars = meta.instance_column();
            let endoscalars_copy = meta.advice_column();
            let word = meta.advice_column();
            let acc = (meta.advice_column(), meta.advice_column());
            let point = (meta.advice_column(), meta.advice_column());
            let base = (meta.advice_column(), meta.advice_column());
            let bits = (meta.advice_column(), meta.advice_column());

            meta.enable_equality(word);

            EndoscaleConfig::<pallas::Affine, 10>::configure(
                meta,
                endoscalars,
                endoscalars_copy,
                word,
                acc,
                point,
                base,
                bits,
                table_config,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<pallas::Base>,
        ) -> Result<(), Error> {
            config.load_endoscale_scalar_table(&mut layouter)?;

            let mut words: Vec<Word<pallas::Base, 10>> = vec![];
            for row in 0..1024 {
                let word =
                    config.get_bitstring(layouter.namespace(|| format!("row {}", row)), row)?;
                words.push(word);
            }

            let g_lagrange = Params::<pallas::Affine>::new(11).g_lagrange();
            let mut acc = None;
            for idx in 0..20 {
                acc = Some(config.endoscale_base_fixed(
                    layouter.namespace(|| format!("commit to {} word", idx)),
                    g_lagrange[idx],
                    &words[idx],
                    acc,
                )?);
            }

            // Load a field element.
            let field_elem = config.load_private(
                layouter.namespace(|| "load field element"),
                config.word,
                Some(pallas::Base::from(1 << 59)),
            )?;
            config.endoscale_base_var::<_, 60>(
                layouter.namespace(|| "commit to field element"),
                g_lagrange,
                field_elem,
                acc,
            )?;

            Ok(())
        }
    }

    impl Circuit<vesta::Base> for MyCircuit<vesta::Base> {
        type Config = EndoscaleConfig<vesta::Affine, 10>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<vesta::Base>) -> Self::Config {
            let table_config = TableConfig::configure(meta);

            let _ = meta.instance_column();
            let constants = meta.fixed_column();
            meta.enable_constant(constants);
            let endoscalars = meta.instance_column();
            let endoscalars_copy = meta.advice_column();
            let word = meta.advice_column();
            let acc = (meta.advice_column(), meta.advice_column());
            let point = (meta.advice_column(), meta.advice_column());
            let base = (meta.advice_column(), meta.advice_column());
            let bits = (meta.advice_column(), meta.advice_column());

            meta.enable_equality(word);

            EndoscaleConfig::<vesta::Affine, 10>::configure(
                meta,
                endoscalars,
                endoscalars_copy,
                word,
                acc,
                point,
                base,
                bits,
                table_config,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<vesta::Base>,
        ) -> Result<(), Error> {
            config.load_endoscale_scalar_table(&mut layouter)?;

            // The max no. of 255-bit scalars that can fit into 1024 rows is 39.
            // Each of these scalars is encoded as 26 endoscalars.
            // We check 26 * 39 = 1014 endoscalars.
            let mut words: Vec<Word<vesta::Base, 10>> = vec![];
            for row in 0..1014 {
                let word =
                    config.get_bitstring(layouter.namespace(|| format!("row {}", row)), row)?;
                words.push(word);
            }

            let g_lagrange = Params::<vesta::Affine>::new(11).g_lagrange();
            let mut acc = None;
            for idx in 0..20 {
                acc = Some(config.endoscale_base_fixed(
                    layouter.namespace(|| format!("commit to {} word", idx)),
                    g_lagrange[idx],
                    &words[idx],
                    acc,
                )?);
            }

            // Load a field element.
            let field_elem = config.load_private(
                layouter.namespace(|| "load field element"),
                config.word,
                Some(vesta::Base::from(1 << 59)),
            )?;
            config.endoscale_base_var::<_, 60>(
                layouter.namespace(|| "commit to field element"),
                g_lagrange,
                field_elem,
                acc,
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_endoscale() {
        use super::super::primitive::endoscale_scalar_with_padding;
        use ff::{Field, PrimeField, PrimeFieldBits};
        use halo2_proofs::dev::MockProver;

        let fp_circuit = MyCircuit::<pallas::Base>(PhantomData);
        let fq_circuit = MyCircuit::<vesta::Base>(PhantomData);

        let fp_pub_inputs = (0..39)
            .map(|_| pallas::Base::random(rand::rngs::OsRng))
            .collect::<Vec<_>>();
        let fq_pub_inputs = (0..39)
            .map(|_| vesta::Base::random(rand::rngs::OsRng))
            .collect::<Vec<_>>();

        let fp_prover = MockProver::run(
            11,
            &fp_circuit,
            vec![
                fp_pub_inputs.clone(),
                primitive::fp::TABLE
                    .iter()
                    .map(|(_, scalar)| *scalar)
                    .collect(),
            ],
        )
        .unwrap();
        assert_eq!(fp_prover.verify(), Ok(()));

        // Encode fp_pub_inputs as public inputs in Fq.
        let fp_pub_inputs_enc = fp_pub_inputs
            .iter()
            .map(|fp_elem| {
                endoscale_scalar_with_padding::<vesta::Base, 10>(
                    &fp_elem
                        .to_le_bits()
                        .iter()
                        .by_val()
                        .take(pallas::Base::NUM_BITS as usize)
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect::<Vec<_>>();

        // Provide encoded Fp public inputs as endoscalars to the Fq circuit.
        let fq_prover =
            MockProver::run(11, &fq_circuit, vec![fq_pub_inputs, fp_pub_inputs_enc]).unwrap();
        assert_eq!(fq_prover.verify(), Ok(()));
    }
}
