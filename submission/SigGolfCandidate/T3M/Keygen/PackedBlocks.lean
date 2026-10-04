import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def signCodeChunks : List (List (BitVec 32)) := [Images.signCode_0, Images.signCode_1, Images.signCode_2, Images.signCode_3, Images.signCode_4, Images.signCode_5, Images.signCode_6, Images.signCode_7, Images.signCode_8, Images.signCode_9, Images.signCode_10, Images.signCode_11, Images.signCode_12, Images.signCode_13, Images.signCode_14, Images.signCode_15, Images.signCode_16, Images.signCode_17, Images.signCode_18, Images.signCode_19, Images.signCode_20, Images.signCode_21, Images.signCode_22, Images.signCode_23, Images.signCode_24, Images.signCode_25, Images.signCode_26, Images.signCode_27, Images.signCode_28, Images.signCode_29, Images.signCode_30, Images.signCode_31, Images.signCode_32, Images.signCode_33, Images.signCode_34, Images.signCode_35, Images.signCode_36, Images.signCode_37, Images.signCode_38, Images.signCode_39, Images.signCode_40, Images.signCode_41, Images.signCode_42]
private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
theorem signCode_flatten : Images.signCode = signCodeChunks.flatten := by
  change signCodeChunks.foldl (· ++ ·) [] = signCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_sign_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (signCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.signImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.signCode.drop b).take code.length = code
  rw [signCode_flatten]
  exact h
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def expandCodeChunks : List (List (BitVec 32)) := [Images.expandCode_0, Images.expandCode_1, Images.expandCode_2, Images.expandCode_3, Images.expandCode_4, Images.expandCode_5, Images.expandCode_6, Images.expandCode_7, Images.expandCode_8, Images.expandCode_9, Images.expandCode_10, Images.expandCode_11, Images.expandCode_12, Images.expandCode_13, Images.expandCode_14, Images.expandCode_15, Images.expandCode_16, Images.expandCode_17, Images.expandCode_18, Images.expandCode_19, Images.expandCode_20, Images.expandCode_21, Images.expandCode_22, Images.expandCode_23, Images.expandCode_24, Images.expandCode_25, Images.expandCode_26, Images.expandCode_27, Images.expandCode_28, Images.expandCode_29, Images.expandCode_30, Images.expandCode_31, Images.expandCode_32, Images.expandCode_33, Images.expandCode_34, Images.expandCode_35, Images.expandCode_36, Images.expandCode_37, Images.expandCode_38, Images.expandCode_39, Images.expandCode_40, Images.expandCode_41, Images.expandCode_42, Images.expandCode_43, Images.expandCode_44, Images.expandCode_45, Images.expandCode_46, Images.expandCode_47, Images.expandCode_48, Images.expandCode_49, Images.expandCode_50, Images.expandCode_51, Images.expandCode_52, Images.expandCode_53, Images.expandCode_54, Images.expandCode_55, Images.expandCode_56, Images.expandCode_57, Images.expandCode_58, Images.expandCode_59, Images.expandCode_60, Images.expandCode_61, Images.expandCode_62, Images.expandCode_63, Images.expandCode_64, Images.expandCode_65, Images.expandCode_66, Images.expandCode_67, Images.expandCode_68, Images.expandCode_69, Images.expandCode_70, Images.expandCode_71, Images.expandCode_72, Images.expandCode_73, Images.expandCode_74, Images.expandCode_75, Images.expandCode_76, Images.expandCode_77, Images.expandCode_78, Images.expandCode_79, Images.expandCode_80, Images.expandCode_81, Images.expandCode_82, Images.expandCode_83, Images.expandCode_84, Images.expandCode_85, Images.expandCode_86, Images.expandCode_87, Images.expandCode_88, Images.expandCode_89, Images.expandCode_90, Images.expandCode_91, Images.expandCode_92, Images.expandCode_93, Images.expandCode_94, Images.expandCode_95, Images.expandCode_96, Images.expandCode_97, Images.expandCode_98, Images.expandCode_99, Images.expandCode_100, Images.expandCode_101, Images.expandCode_102, Images.expandCode_103, Images.expandCode_104, Images.expandCode_105, Images.expandCode_106, Images.expandCode_107, Images.expandCode_108, Images.expandCode_109, Images.expandCode_110, Images.expandCode_111, Images.expandCode_112, Images.expandCode_113, Images.expandCode_114, Images.expandCode_115, Images.expandCode_116, Images.expandCode_117, Images.expandCode_118, Images.expandCode_119, Images.expandCode_120, Images.expandCode_121, Images.expandCode_122, Images.expandCode_123, Images.expandCode_124, Images.expandCode_125, Images.expandCode_126, Images.expandCode_127, Images.expandCode_128, Images.expandCode_129, Images.expandCode_130, Images.expandCode_131, Images.expandCode_132, Images.expandCode_133, Images.expandCode_134, Images.expandCode_135, Images.expandCode_136, Images.expandCode_137, Images.expandCode_138, Images.expandCode_139, Images.expandCode_140, Images.expandCode_141, Images.expandCode_142, Images.expandCode_143, Images.expandCode_144, Images.expandCode_145, Images.expandCode_146, Images.expandCode_147, Images.expandCode_148, Images.expandCode_149, Images.expandCode_150, Images.expandCode_151, Images.expandCode_152, Images.expandCode_153, Images.expandCode_154, Images.expandCode_155, Images.expandCode_156, Images.expandCode_157, Images.expandCode_158, Images.expandCode_159, Images.expandCode_160, Images.expandCode_161, Images.expandCode_162]
theorem expandCode_flatten : Images.expandCode = expandCodeChunks.flatten := by
  change expandCodeChunks.foldl (· ++ ·) [] = expandCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_expand_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.expandCode.drop b).take code.length = code
  rw [expandCode_flatten]
  exact h
end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance
def keygen_entry : List (BitVec 32) := [0x7340006f]
theorem codeAt_keygen_entry : CodeAt Images.keygenImage (pcOf 126) keygen_entry := by decide +kernel
sym_block run_keygen_entry := symRun { noAlias := true } keygen_entry (pcOf 126) 100
theorem steps_keygen_entry (s : MachineState) (hpc : s.pc = pcOf 126) :
    Steps Images.keygenImage s 1 1 (run_keygen_entry.res.toState s) := by
  exact symRun_sound run_keygen_entry codeAt_keygen_entry s hpc (by simp [run_keygen_entry.res, rv_simp])
def keygen_layer0 : List (BitVec 32) := [0x00c00393, 0x00040a63]
theorem codeAt_keygen_layer0 : CodeAt Images.keygenImage (pcOf 587) keygen_layer0 := by decide +kernel
sym_block run_keygen_layer0 := symRun { noAlias := true } keygen_layer0 (pcOf 587) 100
theorem steps_keygen_layer0 (s : MachineState) (hpc : s.pc = pcOf 587) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer0.res.toState s) := by
  exact symRun_sound run_keygen_layer0 codeAt_keygen_layer0 s hpc (by simp [run_keygen_layer0.res, rv_simp])
def keygen_layer1 : List (BitVec 32) := [0x00100393, 0x00740463]
theorem codeAt_keygen_layer1 : CodeAt Images.keygenImage (pcOf 589) keygen_layer1 := by decide +kernel
sym_block run_keygen_layer1 := symRun { noAlias := true } keygen_layer1 (pcOf 589) 100
theorem steps_keygen_layer1 (s : MachineState) (hpc : s.pc = pcOf 589) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer1.res.toState s) := by
  exact symRun_sound run_keygen_layer1 codeAt_keygen_layer1 s hpc (by simp [run_keygen_layer1.res, rv_simp])
def keygen_layer23 : List (BitVec 32) := [0x00000393, 0x00638393]
theorem codeAt_keygen_layer23 : CodeAt Images.keygenImage (pcOf 591) keygen_layer23 := by decide +kernel
sym_block run_keygen_layer23 := symRun { noAlias := true } keygen_layer23 (pcOf 591) 100
theorem steps_keygen_layer23 (s : MachineState) (hpc : s.pc = pcOf 591) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer23.res.toState s) := by
  exact symRun_sound run_keygen_layer23 codeAt_keygen_layer23 s hpc (by simp [run_keygen_layer23.res, rv_simp])
def keygen_inc : List (BitVec 32) := [0x00638393]
theorem codeAt_keygen_inc : CodeAt Images.keygenImage (pcOf 592) keygen_inc := by decide +kernel
sym_block run_keygen_inc := symRun { noAlias := true } keygen_inc (pcOf 592) 100
theorem steps_keygen_inc (s : MachineState) (hpc : s.pc = pcOf 592) :
    Steps Images.keygenImage s 1 1 (run_keygen_inc.res.toState s) := by
  exact symRun_sound run_keygen_inc codeAt_keygen_inc s hpc (by simp [run_keygen_inc.res, rv_simp])
def keygen_body : List (BitVec 32) := [0x00749333, 0x01230333, 0x00020e37, 0x1a0e0e13, 0x02035393, 0x007e3c23, 0x02031313, 0x01035313, 0x03041393, 0x00736333, 0x0c100f13, 0x038f1f13, 0x01e36333, 0x0ffa7393, 0x00839393, 0x00736333, 0x0809e393, 0x00736333, 0x885ff06f]
theorem codeAt_keygen_body : CodeAt Images.keygenImage (pcOf 593) keygen_body := by decide +kernel
sym_block run_keygen_body := symRun { noAlias := true } keygen_body (pcOf 593) 100
theorem steps_keygen_body (s : MachineState) (hpc : s.pc = pcOf 593) :
    Steps Images.keygenImage s 19 19 (run_keygen_body.res.toState s) := by
  exact symRun_sound run_keygen_body codeAt_keygen_body s hpc (by simp [run_keygen_body.res, rv_simp])
def keygen_store : List (BitVec 32) := [0x00020e37, 0x1a0e0e13, 0x006e3823, 0x00020537, 0x1a050513, 0x04000593, 0x00020637, 0x1d060613]
theorem codeAt_keygen_store : CodeAt Images.keygenImage (pcOf 132) keygen_store := by decide +kernel
sym_block run_keygen_store := symRun { noAlias := true } keygen_store (pcOf 132) 100
theorem steps_keygen_store (s : MachineState) (hpc : s.pc = pcOf 132) :
    Steps Images.keygenImage s 8 8 (run_keygen_store.res.toState s) := by
  exact symRun_sound run_keygen_store codeAt_keygen_store s hpc (by simp [run_keygen_store.res, rv_simp])
def sign_entry : List (BitVec 32) := [0x7340006f]
theorem codeAt_sign_entry : CodeAt Images.signImage (pcOf 1022) sign_entry :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_entry := symRun { noAlias := true } sign_entry (pcOf 1022) 100
theorem steps_sign_entry (s : MachineState) (hpc : s.pc = pcOf 1022) :
    Steps Images.signImage s 1 1 (run_sign_entry.res.toState s) := by
  exact symRun_sound run_sign_entry codeAt_sign_entry s hpc (by simp [run_sign_entry.res, rv_simp])
def sign_layer0 : List (BitVec 32) := [0x00c00393, 0x00040a63]
theorem codeAt_sign_layer0 : CodeAt Images.signImage (pcOf 1483) sign_layer0 :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_layer0 := symRun { noAlias := true } sign_layer0 (pcOf 1483) 100
theorem steps_sign_layer0 (s : MachineState) (hpc : s.pc = pcOf 1483) :
    Steps Images.signImage s 2 2 (run_sign_layer0.res.toState s) := by
  exact symRun_sound run_sign_layer0 codeAt_sign_layer0 s hpc (by simp [run_sign_layer0.res, rv_simp])
def sign_layer1 : List (BitVec 32) := [0x00100393, 0x00740463]
theorem codeAt_sign_layer1 : CodeAt Images.signImage (pcOf 1485) sign_layer1 :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_layer1 := symRun { noAlias := true } sign_layer1 (pcOf 1485) 100
theorem steps_sign_layer1 (s : MachineState) (hpc : s.pc = pcOf 1485) :
    Steps Images.signImage s 2 2 (run_sign_layer1.res.toState s) := by
  exact symRun_sound run_sign_layer1 codeAt_sign_layer1 s hpc (by simp [run_sign_layer1.res, rv_simp])
def sign_layer23 : List (BitVec 32) := [0x00000393, 0x00638393]
theorem codeAt_sign_layer23 : CodeAt Images.signImage (pcOf 1487) sign_layer23 :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_layer23 := symRun { noAlias := true } sign_layer23 (pcOf 1487) 100
theorem steps_sign_layer23 (s : MachineState) (hpc : s.pc = pcOf 1487) :
    Steps Images.signImage s 2 2 (run_sign_layer23.res.toState s) := by
  exact symRun_sound run_sign_layer23 codeAt_sign_layer23 s hpc (by simp [run_sign_layer23.res, rv_simp])
def sign_inc : List (BitVec 32) := [0x00638393]
theorem codeAt_sign_inc : CodeAt Images.signImage (pcOf 1488) sign_inc :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_inc := symRun { noAlias := true } sign_inc (pcOf 1488) 100
theorem steps_sign_inc (s : MachineState) (hpc : s.pc = pcOf 1488) :
    Steps Images.signImage s 1 1 (run_sign_inc.res.toState s) := by
  exact symRun_sound run_sign_inc codeAt_sign_inc s hpc (by simp [run_sign_inc.res, rv_simp])
def sign_body : List (BitVec 32) := [0x00749333, 0x01230333, 0x00020e37, 0x1a0e0e13, 0x02035393, 0x007e3c23, 0x02031313, 0x01035313, 0x03041393, 0x00736333, 0x0c100f13, 0x038f1f13, 0x01e36333, 0x0ffa7393, 0x00839393, 0x00736333, 0x0809e393, 0x00736333, 0x885ff06f]
theorem codeAt_sign_body : CodeAt Images.signImage (pcOf 1489) sign_body :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_body := symRun { noAlias := true } sign_body (pcOf 1489) 100
theorem steps_sign_body (s : MachineState) (hpc : s.pc = pcOf 1489) :
    Steps Images.signImage s 19 19 (run_sign_body.res.toState s) := by
  exact symRun_sound run_sign_body codeAt_sign_body s hpc (by simp [run_sign_body.res, rv_simp])
def sign_store : List (BitVec 32) := [0x00020e37, 0x1a0e0e13, 0x006e3823, 0x00020537, 0x1a050513, 0x04000593, 0x00020637, 0x1d060613]
theorem codeAt_sign_store : CodeAt Images.signImage (pcOf 1028) sign_store :=
  codeAt_sign_slice (by decide +kernel) (by kernel_rfl)
sym_block run_sign_store := symRun { noAlias := true } sign_store (pcOf 1028) 100
theorem steps_sign_store (s : MachineState) (hpc : s.pc = pcOf 1028) :
    Steps Images.signImage s 8 8 (run_sign_store.res.toState s) := by
  exact symRun_sound run_sign_store codeAt_sign_store s hpc (by simp [run_sign_store.res, rv_simp])
def expand_entry : List (BitVec 32) := [0x3352706f]
theorem codeAt_expand_entry : CodeAt Images.expandImage (pcOf 1032) expand_entry :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_entry := symRun { noAlias := true } expand_entry (pcOf 1032) 100
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps Images.expandImage s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry codeAt_expand_entry s hpc (by simp [run_expand_entry.res, rv_simp])
def expand_layer0 : List (BitVec 32) := [0x00c00393, 0x00040a63]
theorem codeAt_expand_layer0 : CodeAt Images.expandImage (pcOf 41685) expand_layer0 :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_layer0 := symRun { noAlias := true } expand_layer0 (pcOf 41685) 100
theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 41685) :
    Steps Images.expandImage s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 codeAt_expand_layer0 s hpc (by simp [run_expand_layer0.res, rv_simp])
def expand_layer1 : List (BitVec 32) := [0x00100393, 0x00740463]
theorem codeAt_expand_layer1 : CodeAt Images.expandImage (pcOf 41687) expand_layer1 :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_layer1 := symRun { noAlias := true } expand_layer1 (pcOf 41687) 100
theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 41687) :
    Steps Images.expandImage s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 codeAt_expand_layer1 s hpc (by simp [run_expand_layer1.res, rv_simp])
def expand_layer23 : List (BitVec 32) := [0x00000393, 0x00638393]
theorem codeAt_expand_layer23 : CodeAt Images.expandImage (pcOf 41689) expand_layer23 :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_layer23 := symRun { noAlias := true } expand_layer23 (pcOf 41689) 100
theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 41689) :
    Steps Images.expandImage s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 codeAt_expand_layer23 s hpc (by simp [run_expand_layer23.res, rv_simp])
def expand_inc : List (BitVec 32) := [0x00638393]
theorem codeAt_expand_inc : CodeAt Images.expandImage (pcOf 41690) expand_inc :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_inc := symRun { noAlias := true } expand_inc (pcOf 41690) 100
theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 41690) :
    Steps Images.expandImage s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc codeAt_expand_inc s hpc (by simp [run_expand_inc.res, rv_simp])
def expand_body : List (BitVec 32) := [0x00749333, 0x01230333, 0x00020e37, 0x1a0e0e13, 0x02035393, 0x007e3c23, 0x02031313, 0x01035313, 0x03041393, 0x00736333, 0x0c100f13, 0x038f1f13, 0x01e36333, 0x0ffa7393, 0x00839393, 0x00736333, 0x0809e393, 0x00736333, 0xc84d806f]
theorem codeAt_expand_body : CodeAt Images.expandImage (pcOf 41691) expand_body :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_body := symRun { noAlias := true } expand_body (pcOf 41691) 100
theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 41691) :
    Steps Images.expandImage s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body codeAt_expand_body s hpc (by simp [run_expand_body.res, rv_simp])
def expand_store : List (BitVec 32) := [0x00020e37, 0x1a0e0e13, 0x006e3823, 0x00020537, 0x1a050513, 0x04000593, 0x00020637, 0x1d060613]
theorem codeAt_expand_store : CodeAt Images.expandImage (pcOf 1038) expand_store :=
  codeAt_expand_slice (by decide +kernel) (by kernel_rfl)
sym_block run_expand_store := symRun { noAlias := true } expand_store (pcOf 1038) 100
theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps Images.expandImage s 8 8 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store codeAt_expand_store s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Keygen.PackedBlocks
