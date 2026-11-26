module

public import Staircase.WindowCheck

@[expose] public section
namespace Staircase.WindowData.R003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rule : Rule := ⟨⟨[1, 0, 0],1⟩,7⟩
def origins : OriginCert := ⟨3,0x1047,#[
⟨#[2,3,4,5],#[⟨0x1,⟨1,1,(.leaf 0x1)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[10,11,12,13],#[⟨0x40,⟨1,7,(.leaf 0x40)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[0,9],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩,⟨0x1000,⟨1,13,(.leaf 0x1000)⟩⟩],⟨4,4,(.leaf 0x864)⟩,1024⟩,
⟨#[0,8,9],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩,⟨0x1000,⟨1,19,(.leaf 0x40000)⟩⟩],⟨4,5,(.leaf 0x41aa)⟩,1024⟩,
⟨#[0,7,8],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩,⟨0x1000,⟨1,25,(.leaf 0x1000000)⟩⟩],⟨4,5,(.leaf 0x66d3)⟩,1024⟩,
⟨#[0,6,7],#[⟨0x2,⟨1,2,(.leaf 0x2)⟩⟩,⟨0x1000,⟨1,31,(.leaf 0x40000000)⟩⟩],⟨4,6,(.leaf 0x227dc)⟩,1024⟩,
⟨#[5,13],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x1002,⟨1,31,(.leaf 0x40000002)⟩⟩],⟨4,6,(.leaf 0x27940)⟩,0⟩,
⟨#[4,5,12,13],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x1002,⟨2,31,(.leaf 0x2000000101000002)⟩⟩],⟨4,6,(.leaf 0x31a40)⟩,0⟩,
⟨#[3,4,11,12],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x1002,⟨2,25,(.leaf 0x2000004040002)⟩⟩],⟨4,7,(.leaf 0x105c80)⟩,0⟩,
⟨#[2,3,10,11],#[⟨0x4,⟨1,3,(.leaf 0x4)⟩⟩,⟨0x1002,⟨2,19,(.leaf 0x2000101002)⟩⟩],⟨4,7,(.leaf 0x146480)⟩,0⟩,
⟨#[9,1],#[⟨0x1006,⟨2,19,(.leaf 0x2000301006)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[8,9,1],#[⟨0x1006,⟨3,25,(.leaf 0x400001808000c001006)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[7,8,1],#[⟨0x1006,⟨3,31,(.leaf 0x100000018080000300040006)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩,
⟨#[6,7,1],#[⟨0x1006,⟨2,31,(.leaf 0x2000000301000006)⟩⟩],⟨1,1,(.leaf 0x0)⟩,0⟩],⟨89,11,(.fork (.fork (.leaf 0x80300000401800000000000010060000080300000000000002000008000000000000000000000) (.leaf 0x1003000000000000020000100300000000000002000010050000000000200200001)) (.leaf 0x50000000000200200001005000000000020020000100500000000002002000018000060040180000200c00))⟩⟩
def boxes : BoxProof := (.cut 2 1 (.cut 3 1 (.miss 10 0x41000047) (.miss 13 0x40047)) (.miss 13 0x1047))

theorem valid : rule.Valid := checkWindow_sound origins boxes rule (by decide +kernel)

def rules : List Rule := [rule]
theorem all_valid (r : Rule) (h : r ∈ rules) : r.Valid := by
  have eq : r=rule := by simpa [rules] using h
  exact eq ▸ valid

end Staircase.WindowData.R003
