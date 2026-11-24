import StarFiring.Core

namespace StarFiring.Padding

/-- A strict excedance of the permutation. Fixed points are put on the low track. -/
abbrev High (w : Row n → Row n) (i : Row n) : Prop := i < w i

end StarFiring.Padding
