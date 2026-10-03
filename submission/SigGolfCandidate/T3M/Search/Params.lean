import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3M.Search
/-- Producer register `s11`: the split after 51 radix-five top digits; zero for lower layers. -/
def csN4 (lay : T3.Layer) : Nat := if lay = 0 then 51 else 0
end SigGolfCandidate.T3M.Search
