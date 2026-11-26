module

public import Staircase.WindowCheck

@[expose] public section
namespace Staircase.WindowData.R001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rule : Rule := ⟨⟨[0, 1, 0],7⟩,1⟩
def origins : OriginCert := ⟨3,0x401c1,#[
⟨#[2,3,4,5],#[⟨0x1,⟨1,1,(.leaf 0x1)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[10,11,12,13],#[⟨0x40,⟨1,7,(.leaf 0x40)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,9],#[⟨0x40100,⟨1,55,(.leaf 0x40000000000100)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,8,9],#[⟨0x40100,⟨2,55,(.leaf 0x2000000000008001000000000100)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,7,8],#[⟨0x40100,⟨2,49,(.leaf 0x2000000000200040000000100)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,6,7],#[⟨0x40100,⟨2,43,(.leaf 0x2000000008001000000100)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[5,13],#[⟨0x100,⟨1,9,(.leaf 0x100)⟩⟩,⟨0x40000,⟨1,37,(.leaf 0x1000000000)⟩⟩],⟨4,3,(.leaf 0x1a0)⟩,1024⟩,
⟨#[4,5,12,13],#[⟨0x100,⟨1,9,(.leaf 0x100)⟩⟩,⟨0x40000,⟨1,43,(.leaf 0x40000000000)⟩⟩],⟨4,4,(.leaf 0xc80)⟩,1024⟩,
⟨#[3,4,11,12],#[⟨0x100,⟨1,9,(.leaf 0x100)⟩⟩,⟨0x40000,⟨1,49,(.leaf 0x1000000000000)⟩⟩],⟨4,5,(.leaf 0x5200)⟩,1024⟩,
⟨#[2,3,10,11],#[⟨0x100,⟨1,9,(.leaf 0x100)⟩⟩,⟨0x40000,⟨1,55,(.leaf 0x40000000000000)⟩⟩],⟨4,5,(.leaf 0x7300)⟩,1024⟩,
⟨#[9,1],#[⟨0x80,⟨1,8,(.leaf 0x80)⟩⟩],⟨1,6,(.leaf 0x20)⟩,0⟩,
⟨#[8,9,1],#[⟨0x80,⟨1,8,(.leaf 0x80)⟩⟩],⟨1,6,(.leaf 0x22)⟩,0⟩,
⟨#[7,8,1],#[⟨0x80,⟨1,8,(.leaf 0x80)⟩⟩],⟨1,6,(.leaf 0x25)⟩,0⟩,
⟨#[6,7,1],#[⟨0x80,⟨1,8,(.leaf 0x80)⟩⟩],⟨1,6,(.leaf 0x28)⟩,0⟩],⟨43,1,(.fork (.leaf 0x22222200) (.leaf 0x0))⟩⟩
def boxes : BoxProof := (.cut 9 1 (.miss 2 0x10410000001c1) (.miss 4 0x400000000001c1))

theorem valid : rule.Valid := checkWindow_sound origins boxes rule (by decide +kernel)

def rules : List Rule := [rule]
theorem all_valid (r : Rule) (h : r ∈ rules) : r.Valid := by
  have eq : r=rule := by simpa [rules] using h
  exact eq ▸ valid

end Staircase.WindowData.R001
