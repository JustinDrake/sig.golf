namespace CertificateBase

theorem helper : True := True.intro

end CertificateBase

namespace SigGolf.Challenge

def trustedLiteral : Nat := 17
def submission : Nat := 17
theorem certificate : submission = 17 := rfl
theorem image_binding : submission = trustedLiteral := rfl

inductive Box where
  | mk (value : Nat)

def box : Box := .mk 17
theorem box_certificate : box = .mk 17 := rfl

end SigGolf.Challenge
