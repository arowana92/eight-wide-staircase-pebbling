module

public import Staircase.WindowCheck

@[expose] public section
namespace Staircase.WindowData.R002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rule : Rule := ⟨⟨[0, 1, 0],1⟩,7⟩
def origins : OriginCert := ⟨3,0x40047,#[
⟨#[2,3,4,5],#[⟨0x1,⟨1,1,(.leaf 0x1)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[10,11,12,13],#[⟨0x40,⟨1,7,(.leaf 0x40)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,9],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩],⟨1,3,(.leaf 0x4)⟩,0⟩,
⟨#[0,8,9],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩],⟨1,3,(.leaf 0x6)⟩,0⟩,
⟨#[0,7,8],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩],⟨1,4,(.leaf 0x9)⟩,0⟩,
⟨#[0,6,7],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩],⟨1,4,(.leaf 0xc)⟩,0⟩,
⟨#[5,13],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x40000,⟨1,37,(.leaf 0x1000000000)⟩⟩],⟨4,5,(.leaf 0x45e0)⟩,1024⟩,
⟨#[4,5,12,13],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x40000,⟨1,43,(.leaf 0x40000000000)⟩⟩],⟨4,5,(.leaf 0x5e60)⟩,1024⟩,
⟨#[3,4,11,12],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x40000,⟨1,49,(.leaf 0x1000000000000)⟩⟩],⟨4,5,(.leaf 0x7f60)⟩,1024⟩,
⟨#[2,3,10,11],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x40000,⟨1,55,(.leaf 0x40000000000000)⟩⟩],⟨4,6,(.leaf 0x278c0)⟩,1024⟩,
⟨#[9,1],#[⟨0x40004,⟨1,55,(.leaf 0x40000000000004)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[8,9,1],#[⟨0x40004,⟨2,55,(.leaf 0x2000000000000201000000000004)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[7,8,1],#[⟨0x40004,⟨2,49,(.leaf 0x2000000000008040000000004)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[6,7,1],#[⟨0x40004,⟨2,43,(.leaf 0x2000000000201000000004)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩],⟨43,1,(.fork (.leaf 0x44400000) (.leaf 0x444))⟩⟩
def boxes : BoxProof := (.cut 9 1 (.miss 10 0x1041000000047) (.miss 12 0x40000000000047))

theorem valid : rule.Valid := checkWindow_sound origins boxes rule (by decide +kernel)

def rules : List Rule := [rule]
theorem all_valid (r : Rule) (h : r ∈ rules) : r.Valid := by
  have eq : r=rule := by simpa [rules] using h
  exact eq ▸ valid

end Staircase.WindowData.R002
