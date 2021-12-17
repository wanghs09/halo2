//! Gadget for endoscaling.

use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use pasta_curves::arithmetic::CurveAffine;

pub mod primitive;

/// Instructions to map bitstrings to and from endoscalars.
///
/// TODO: Replace N = 2^K once we have const evaluable.
pub trait EndoscaleInstructions<C: CurveAffine, const K: usize, const N: usize>
where
    C::Base: EndoscaleLookup<K, N>,
{
    /// A K-bit word.
    type Word;

    /// A commitment to a bitstring.
    type Commitment;

    /// Loads endoscale scalar table.
    fn load_endoscale_scalar_table(
        &self,
        layouter: &mut impl Layouter<C::Base>,
    ) -> Result<(), Error>;

    /// Gets a bitstring from its endoscalar representation.
    ///
    /// These endoscalars are provided as the cells in the public input column.
    fn get_bitstring(
        &self,
        layouter: impl Layouter<C::Base>,
        row: usize,
    ) -> Result<Self::Word, Error>;

    /// Compute commitment to a K-bit word using the endoscaling algorithm.
    fn endoscale_base_fixed(
        &self,
        layouter: impl Layouter<C::Base>,
        base: C,
        word: &Self::Word,
        prev_acc: Option<Self::Commitment>,
    ) -> Result<Self::Commitment, Error>;

    /// Compute commitment to a variable-length bitstring using the endoscaling
    /// algorithm.
    fn endoscale_base_var<L: Layouter<C::Base>, const NUM_BITS: usize>(
        &self,
        layouter: L,
        bases: Vec<C>,
        field_elem: AssignedCell<C::Base, C::Base>,
        prev_acc: Option<Self::Commitment>,
    ) -> Result<Self::Commitment, Error>;
}

/// A trait providing the lookup table for decoding endoscalars.
pub trait EndoscaleLookup<const K: usize, const N: usize>
where
    Self: std::marker::Sized,
{
    /// A lookup table mapping `K`-bit values to endoscalars.
    fn table() -> [([bool; K], Self); N];
}
