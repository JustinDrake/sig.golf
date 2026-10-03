import SigGolfCandidate.T3M.Images.Verify
import SigGolfCandidate.T3M.Mem

/-! # V1 chains: code access, label tables and the expected symbolic results of the chain code

The chain code of the verify image (`t3m/ver/gen_t3.py`: `chains_code`, `_ttab`, `_ctab`, `_qtab`, `_q48tab`) is
layer-shared and entered by `jalr` dispatch on the digits:

* **lower layers** (3, 2, 1; 43 chains of width 3): 14 triples `(3t, 3t+1, 3t+2)`; the table `ttab` (512 rows
  `k = dA + 8 dB + 64 dC` of 16 slots of 8 words) holds in slot `t` the head of chain `A = 3t` (digit `dA < 7`)
  or its max-digit copy, then `j` into the shared block `tc_t_dB_dC`: `A`'s rungs `r0 .. r6` (entered at
  `r_dA`), then `B` and `C` (head and rungs `d .. 6`, or the copy), then the extraction and `jalr` of triple
  `t + 1`, or for `t = 13` the dispatch `ctab[t4]` of the checksum chain 42 (`ck_r0 .. ck_r6`, `ck_done`);
* **top layer** (58 chains: 49 of width 2, 9 of width 3): 12 quads `(4q .. 4q+3)` through `qtab` (256 rows of 12
  slots) and the blocks `tq_q_dB_dC_dD`, chain 48 through `q48tab`, then `q48_done` dispatches into the lower
  code's triples 11..13 (the top's chains 49..57 run as the lower chains 33..41), and `ctab[8] = jr ra`.

Chain blocks are addressed from a base register (`s6 = x22`: the lower chains and the top's 49..57; `s3 = x19`:
the top's 0..48). A head is `addi a0, base, off; addi a2, a0, 48; mv s9, s11 | add s9, s9, t3; sd s9, 16(a0);
sd tp, 24(a0)`, a rung `sb POS_d, 20(a0); [li a2, slot]; ecall`, a max-digit copy `ld gp, off+48(base);
ld a4, off+56(base); sd gp, slot; sd a4, slot+8; [mv s9, s11 | add s9, s9, t3]`.

Every expected result is the executor's (`Rv.symRun` from the identity state) on the image words at the given
pc; `ChainCheck*` verifies them by `decide +kernel`. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Code access through the image's 256-word chunks -/

/-- The verify image's chunks (`Images.verifyCode = c₀ ++ c₁ ++ …`). -/
def lChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16, Images.verifyCode_17, Images.verifyCode_18, Images.verifyCode_19, Images.verifyCode_20, Images.verifyCode_21, Images.verifyCode_22, Images.verifyCode_23, Images.verifyCode_24, Images.verifyCode_25, Images.verifyCode_26, Images.verifyCode_27, Images.verifyCode_28, Images.verifyCode_29, Images.verifyCode_30, Images.verifyCode_31, Images.verifyCode_32, Images.verifyCode_33, Images.verifyCode_34, Images.verifyCode_35, Images.verifyCode_36, Images.verifyCode_37, Images.verifyCode_38, Images.verifyCode_39, Images.verifyCode_40, Images.verifyCode_41, Images.verifyCode_42, Images.verifyCode_43, Images.verifyCode_44, Images.verifyCode_45, Images.verifyCode_46, Images.verifyCode_47, Images.verifyCode_48, Images.verifyCode_49, Images.verifyCode_50, Images.verifyCode_51, Images.verifyCode_52, Images.verifyCode_53, Images.verifyCode_54, Images.verifyCode_55, Images.verifyCode_56, Images.verifyCode_57, Images.verifyCode_58, Images.verifyCode_59, Images.verifyCode_60, Images.verifyCode_61, Images.verifyCode_62, Images.verifyCode_63, Images.verifyCode_64, Images.verifyCode_65, Images.verifyCode_66, Images.verifyCode_67, Images.verifyCode_68, Images.verifyCode_69, Images.verifyCode_70, Images.verifyCode_71, Images.verifyCode_72, Images.verifyCode_73, Images.verifyCode_74, Images.verifyCode_75, Images.verifyCode_76, Images.verifyCode_77, Images.verifyCode_78, Images.verifyCode_79, Images.verifyCode_80, Images.verifyCode_81, Images.verifyCode_82, Images.verifyCode_83, Images.verifyCode_84, Images.verifyCode_85, Images.verifyCode_86, Images.verifyCode_87, Images.verifyCode_88, Images.verifyCode_89, Images.verifyCode_90, Images.verifyCode_91, Images.verifyCode_92, Images.verifyCode_93, Images.verifyCode_94, Images.verifyCode_95, Images.verifyCode_96, Images.verifyCode_97, Images.verifyCode_98, Images.verifyCode_99, Images.verifyCode_100, Images.verifyCode_101, Images.verifyCode_102, Images.verifyCode_103, Images.verifyCode_104, Images.verifyCode_105, Images.verifyCode_106, Images.verifyCode_107, Images.verifyCode_108, Images.verifyCode_109, Images.verifyCode_110, Images.verifyCode_111, Images.verifyCode_112, Images.verifyCode_113, Images.verifyCode_114, Images.verifyCode_115, Images.verifyCode_116, Images.verifyCode_117, Images.verifyCode_118, Images.verifyCode_119, Images.verifyCode_120, Images.verifyCode_121, Images.verifyCode_122, Images.verifyCode_123, Images.verifyCode_124, Images.verifyCode_125, Images.verifyCode_126, Images.verifyCode_127, Images.verifyCode_128, Images.verifyCode_129, Images.verifyCode_130, Images.verifyCode_131, Images.verifyCode_132, Images.verifyCode_133, Images.verifyCode_134, Images.verifyCode_135, Images.verifyCode_136, Images.verifyCode_137, Images.verifyCode_138, Images.verifyCode_139, Images.verifyCode_140, Images.verifyCode_141, Images.verifyCode_142, Images.verifyCode_143, Images.verifyCode_144, Images.verifyCode_145, Images.verifyCode_146, Images.verifyCode_147, Images.verifyCode_148, Images.verifyCode_149, Images.verifyCode_150, Images.verifyCode_151, Images.verifyCode_152, Images.verifyCode_153, Images.verifyCode_154, Images.verifyCode_155, Images.verifyCode_156, Images.verifyCode_157, Images.verifyCode_158, Images.verifyCode_159, Images.verifyCode_160, Images.verifyCode_161, Images.verifyCode_162, Images.verifyCode_163, Images.verifyCode_164, Images.verifyCode_165, Images.verifyCode_166, Images.verifyCode_167, Images.verifyCode_168, Images.verifyCode_169, Images.verifyCode_170, Images.verifyCode_171, Images.verifyCode_172, Images.verifyCode_173, Images.verifyCode_174, Images.verifyCode_175, Images.verifyCode_176, Images.verifyCode_177, Images.verifyCode_178, Images.verifyCode_179, Images.verifyCode_180, Images.verifyCode_181, Images.verifyCode_182, Images.verifyCode_183, Images.verifyCode_184, Images.verifyCode_185, Images.verifyCode_186, Images.verifyCode_187, Images.verifyCode_188, Images.verifyCode_189, Images.verifyCode_190, Images.verifyCode_191, Images.verifyCode_192, Images.verifyCode_193, Images.verifyCode_194, Images.verifyCode_195, Images.verifyCode_196, Images.verifyCode_197, Images.verifyCode_198, Images.verifyCode_199, Images.verifyCode_200, Images.verifyCode_201, Images.verifyCode_202, Images.verifyCode_203, Images.verifyCode_204, Images.verifyCode_205, Images.verifyCode_206, Images.verifyCode_207, Images.verifyCode_208, Images.verifyCode_209, Images.verifyCode_210, Images.verifyCode_211, Images.verifyCode_212, Images.verifyCode_213, Images.verifyCode_214, Images.verifyCode_215, Images.verifyCode_216, Images.verifyCode_217, Images.verifyCode_218, Images.verifyCode_219, Images.verifyCode_220, Images.verifyCode_221, Images.verifyCode_222, Images.verifyCode_223, Images.verifyCode_224, Images.verifyCode_225, Images.verifyCode_226, Images.verifyCode_227, Images.verifyCode_228, Images.verifyCode_229, Images.verifyCode_230, Images.verifyCode_231, Images.verifyCode_232, Images.verifyCode_233, Images.verifyCode_234, Images.verifyCode_235, Images.verifyCode_236, Images.verifyCode_237, Images.verifyCode_238, Images.verifyCode_239, Images.verifyCode_240, Images.verifyCode_241, Images.verifyCode_242, Images.verifyCode_243, Images.verifyCode_244, Images.verifyCode_245, Images.verifyCode_246, Images.verifyCode_247, Images.verifyCode_248, Images.verifyCode_249, Images.verifyCode_250, Images.verifyCode_251, Images.verifyCode_252, Images.verifyCode_253, Images.verifyCode_254, Images.verifyCode_255, Images.verifyCode_256, Images.verifyCode_257, Images.verifyCode_258, Images.verifyCode_259, Images.verifyCode_260, Images.verifyCode_261, Images.verifyCode_262, Images.verifyCode_263, Images.verifyCode_264, Images.verifyCode_265, Images.verifyCode_266, Images.verifyCode_267, Images.verifyCode_268, Images.verifyCode_269, Images.verifyCode_270, Images.verifyCode_271, Images.verifyCode_272, Images.verifyCode_273, Images.verifyCode_274, Images.verifyCode_275, Images.verifyCode_276, Images.verifyCode_277, Images.verifyCode_278, Images.verifyCode_279, Images.verifyCode_280, Images.verifyCode_281, Images.verifyCode_282, Images.verifyCode_283, Images.verifyCode_284, Images.verifyCode_285, Images.verifyCode_286, Images.verifyCode_287, Images.verifyCode_288, Images.verifyCode_289, Images.verifyCode_290, Images.verifyCode_291, Images.verifyCode_292, Images.verifyCode_293, Images.verifyCode_294, Images.verifyCode_295, Images.verifyCode_296, Images.verifyCode_297, Images.verifyCode_298, Images.verifyCode_299, Images.verifyCode_300, Images.verifyCode_301, Images.verifyCode_302, Images.verifyCode_303, Images.verifyCode_304, Images.verifyCode_305, Images.verifyCode_306, Images.verifyCode_307, Images.verifyCode_308, Images.verifyCode_309, Images.verifyCode_310, Images.verifyCode_311, Images.verifyCode_312, Images.verifyCode_313, Images.verifyCode_314, Images.verifyCode_315, Images.verifyCode_316, Images.verifyCode_317, Images.verifyCode_318, Images.verifyCode_319, Images.verifyCode_320, Images.verifyCode_321, Images.verifyCode_322, Images.verifyCode_323, Images.verifyCode_324, Images.verifyCode_325, Images.verifyCode_326, Images.verifyCode_327, Images.verifyCode_328, Images.verifyCode_329, Images.verifyCode_330, Images.verifyCode_331, Images.verifyCode_332, Images.verifyCode_333, Images.verifyCode_334, Images.verifyCode_335, Images.verifyCode_336, Images.verifyCode_337, Images.verifyCode_338, Images.verifyCode_339, Images.verifyCode_340, Images.verifyCode_341, Images.verifyCode_342, Images.verifyCode_343, Images.verifyCode_344, Images.verifyCode_345, Images.verifyCode_346, Images.verifyCode_347, Images.verifyCode_348, Images.verifyCode_349, Images.verifyCode_350, Images.verifyCode_351, Images.verifyCode_352, Images.verifyCode_353, Images.verifyCode_354, Images.verifyCode_355, Images.verifyCode_356, Images.verifyCode_357, Images.verifyCode_358, Images.verifyCode_359, Images.verifyCode_360, Images.verifyCode_361, Images.verifyCode_362, Images.verifyCode_363, Images.verifyCode_364, Images.verifyCode_365, Images.verifyCode_366, Images.verifyCode_367, Images.verifyCode_368, Images.verifyCode_369, Images.verifyCode_370, Images.verifyCode_371, Images.verifyCode_372, Images.verifyCode_373, Images.verifyCode_374, Images.verifyCode_375, Images.verifyCode_376, Images.verifyCode_377, Images.verifyCode_378, Images.verifyCode_379, Images.verifyCode_380, Images.verifyCode_381, Images.verifyCode_382, Images.verifyCode_383, Images.verifyCode_384, Images.verifyCode_385, Images.verifyCode_386, Images.verifyCode_387, Images.verifyCode_388, Images.verifyCode_389, Images.verifyCode_390, Images.verifyCode_391, Images.verifyCode_392, Images.verifyCode_393, Images.verifyCode_394, Images.verifyCode_395, Images.verifyCode_396, Images.verifyCode_397, Images.verifyCode_398, Images.verifyCode_399, Images.verifyCode_400, Images.verifyCode_401, Images.verifyCode_402, Images.verifyCode_403, Images.verifyCode_404, Images.verifyCode_405, Images.verifyCode_406, Images.verifyCode_407, Images.verifyCode_408, Images.verifyCode_409, Images.verifyCode_410, Images.verifyCode_411, Images.verifyCode_412, Images.verifyCode_413, Images.verifyCode_414, Images.verifyCode_415, Images.verifyCode_416, Images.verifyCode_417, Images.verifyCode_418, Images.verifyCode_419, Images.verifyCode_420, Images.verifyCode_421, Images.verifyCode_422, Images.verifyCode_423, Images.verifyCode_424, Images.verifyCode_425, Images.verifyCode_426, Images.verifyCode_427, Images.verifyCode_428, Images.verifyCode_429, Images.verifyCode_430, Images.verifyCode_431, Images.verifyCode_432, Images.verifyCode_433, Images.verifyCode_434, Images.verifyCode_435, Images.verifyCode_436, Images.verifyCode_437, Images.verifyCode_438, Images.verifyCode_439, Images.verifyCode_440, Images.verifyCode_441, Images.verifyCode_442, Images.verifyCode_443, Images.verifyCode_444, Images.verifyCode_445, Images.verifyCode_446, Images.verifyCode_447, Images.verifyCode_448, Images.verifyCode_449, Images.verifyCode_450, Images.verifyCode_451, Images.verifyCode_452, Images.verifyCode_453, Images.verifyCode_454, Images.verifyCode_455, Images.verifyCode_456, Images.verifyCode_457, Images.verifyCode_458, Images.verifyCode_459, Images.verifyCode_460, Images.verifyCode_461, Images.verifyCode_462, Images.verifyCode_463, Images.verifyCode_464, Images.verifyCode_465, Images.verifyCode_466, Images.verifyCode_467, Images.verifyCode_468, Images.verifyCode_469, Images.verifyCode_470, Images.verifyCode_471, Images.verifyCode_472, Images.verifyCode_473, Images.verifyCode_474, Images.verifyCode_475, Images.verifyCode_476, Images.verifyCode_477, Images.verifyCode_478, Images.verifyCode_479, Images.verifyCode_480, Images.verifyCode_481, Images.verifyCode_482, Images.verifyCode_483, Images.verifyCode_484, Images.verifyCode_485, Images.verifyCode_486, Images.verifyCode_487, Images.verifyCode_488, Images.verifyCode_489, Images.verifyCode_490, Images.verifyCode_491, Images.verifyCode_492, Images.verifyCode_493, Images.verifyCode_494, Images.verifyCode_495, Images.verifyCode_496, Images.verifyCode_497, Images.verifyCode_498, Images.verifyCode_499, Images.verifyCode_500, Images.verifyCode_501, Images.verifyCode_502, Images.verifyCode_503, Images.verifyCode_504, Images.verifyCode_505, Images.verifyCode_506, Images.verifyCode_507, Images.verifyCode_508, Images.verifyCode_509, Images.verifyCode_510, Images.verifyCode_511, Images.verifyCode_512, Images.verifyCode_513, Images.verifyCode_514, Images.verifyCode_515, Images.verifyCode_516, Images.verifyCode_517, Images.verifyCode_518, Images.verifyCode_519, Images.verifyCode_520, Images.verifyCode_521, Images.verifyCode_522, Images.verifyCode_523, Images.verifyCode_524, Images.verifyCode_525, Images.verifyCode_526, Images.verifyCode_527, Images.verifyCode_528, Images.verifyCode_529, Images.verifyCode_530, Images.verifyCode_531, Images.verifyCode_532, Images.verifyCode_533, Images.verifyCode_534, Images.verifyCode_535, Images.verifyCode_536, Images.verifyCode_537, Images.verifyCode_538, Images.verifyCode_539, Images.verifyCode_540, Images.verifyCode_541, Images.verifyCode_542, Images.verifyCode_543, Images.verifyCode_544, Images.verifyCode_545, Images.verifyCode_546, Images.verifyCode_547, Images.verifyCode_548, Images.verifyCode_549, Images.verifyCode_550, Images.verifyCode_551, Images.verifyCode_552, Images.verifyCode_553, Images.verifyCode_554, Images.verifyCode_555, Images.verifyCode_556, Images.verifyCode_557, Images.verifyCode_558, Images.verifyCode_559, Images.verifyCode_560, Images.verifyCode_561, Images.verifyCode_562, Images.verifyCode_563, Images.verifyCode_564, Images.verifyCode_565, Images.verifyCode_566, Images.verifyCode_567, Images.verifyCode_568, Images.verifyCode_569, Images.verifyCode_570, Images.verifyCode_571, Images.verifyCode_572, Images.verifyCode_573, Images.verifyCode_574, Images.verifyCode_575, Images.verifyCode_576, Images.verifyCode_577, Images.verifyCode_578, Images.verifyCode_579, Images.verifyCode_580, Images.verifyCode_581, Images.verifyCode_582, Images.verifyCode_583, Images.verifyCode_584, Images.verifyCode_585, Images.verifyCode_586, Images.verifyCode_587, Images.verifyCode_588, Images.verifyCode_589, Images.verifyCode_590, Images.verifyCode_591, Images.verifyCode_592, Images.verifyCode_593, Images.verifyCode_594, Images.verifyCode_595, Images.verifyCode_596, Images.verifyCode_597, Images.verifyCode_598, Images.verifyCode_599, Images.verifyCode_600, Images.verifyCode_601, Images.verifyCode_602, Images.verifyCode_603, Images.verifyCode_604, Images.verifyCode_605, Images.verifyCode_606, Images.verifyCode_607, Images.verifyCode_608, Images.verifyCode_609, Images.verifyCode_610, Images.verifyCode_611, Images.verifyCode_612, Images.verifyCode_613, Images.verifyCode_614, Images.verifyCode_615, Images.verifyCode_616, Images.verifyCode_617, Images.verifyCode_618, Images.verifyCode_619, Images.verifyCode_620, Images.verifyCode_621, Images.verifyCode_622, Images.verifyCode_623, Images.verifyCode_624, Images.verifyCode_625, Images.verifyCode_626, Images.verifyCode_627, Images.verifyCode_628, Images.verifyCode_629, Images.verifyCode_630, Images.verifyCode_631, Images.verifyCode_632, Images.verifyCode_633, Images.verifyCode_634, Images.verifyCode_635, Images.verifyCode_636, Images.verifyCode_637, Images.verifyCode_638, Images.verifyCode_639, Images.verifyCode_640, Images.verifyCode_641, Images.verifyCode_642, Images.verifyCode_643, Images.verifyCode_644, Images.verifyCode_645, Images.verifyCode_646, Images.verifyCode_647, Images.verifyCode_648, Images.verifyCode_649, Images.verifyCode_650, Images.verifyCode_651, Images.verifyCode_652, Images.verifyCode_653, Images.verifyCode_654, Images.verifyCode_655, Images.verifyCode_656, Images.verifyCode_657, Images.verifyCode_658, Images.verifyCode_659, Images.verifyCode_660, Images.verifyCode_661, Images.verifyCode_662, Images.verifyCode_663, Images.verifyCode_664, Images.verifyCode_665, Images.verifyCode_666, Images.verifyCode_667, Images.verifyCode_668, Images.verifyCode_669, Images.verifyCode_670, Images.verifyCode_671, Images.verifyCode_672, Images.verifyCode_673, Images.verifyCode_674, Images.verifyCode_675, Images.verifyCode_676, Images.verifyCode_677, Images.verifyCode_678, Images.verifyCode_679, Images.verifyCode_680, Images.verifyCode_681, Images.verifyCode_682, Images.verifyCode_683, Images.verifyCode_684, Images.verifyCode_685, Images.verifyCode_686, Images.verifyCode_687, Images.verifyCode_688, Images.verifyCode_689, Images.verifyCode_690, Images.verifyCode_691, Images.verifyCode_692, Images.verifyCode_693, Images.verifyCode_694, Images.verifyCode_695, Images.verifyCode_696, Images.verifyCode_697, Images.verifyCode_698, Images.verifyCode_699, Images.verifyCode_700, Images.verifyCode_701, Images.verifyCode_702, Images.verifyCode_703, Images.verifyCode_704, Images.verifyCode_705, Images.verifyCode_706, Images.verifyCode_707, Images.verifyCode_708, Images.verifyCode_709, Images.verifyCode_710, Images.verifyCode_711, Images.verifyCode_712, Images.verifyCode_713, Images.verifyCode_714, Images.verifyCode_715, Images.verifyCode_716, Images.verifyCode_717, Images.verifyCode_718, Images.verifyCode_719, Images.verifyCode_720, Images.verifyCode_721, Images.verifyCode_722, Images.verifyCode_723, Images.verifyCode_724, Images.verifyCode_725, Images.verifyCode_726, Images.verifyCode_727, Images.verifyCode_728, Images.verifyCode_729, Images.verifyCode_730, Images.verifyCode_731, Images.verifyCode_732, Images.verifyCode_733, Images.verifyCode_734, Images.verifyCode_735, Images.verifyCode_736, Images.verifyCode_737, Images.verifyCode_738, Images.verifyCode_739, Images.verifyCode_740, Images.verifyCode_741, Images.verifyCode_742, Images.verifyCode_743, Images.verifyCode_744, Images.verifyCode_745, Images.verifyCode_746, Images.verifyCode_747, Images.verifyCode_748, Images.verifyCode_749, Images.verifyCode_750, Images.verifyCode_751, Images.verifyCode_752, Images.verifyCode_753, Images.verifyCode_754, Images.verifyCode_755, Images.verifyCode_756, Images.verifyCode_757, Images.verifyCode_758, Images.verifyCode_759, Images.verifyCode_760, Images.verifyCode_761, Images.verifyCode_762, Images.verifyCode_763, Images.verifyCode_764, Images.verifyCode_765, Images.verifyCode_766, Images.verifyCode_767, Images.verifyCode_768, Images.verifyCode_769, Images.verifyCode_770, Images.verifyCode_771, Images.verifyCode_772, Images.verifyCode_773, Images.verifyCode_774, Images.verifyCode_775, Images.verifyCode_776, Images.verifyCode_777, Images.verifyCode_778, Images.verifyCode_779, Images.verifyCode_780, Images.verifyCode_781, Images.verifyCode_782, Images.verifyCode_783, Images.verifyCode_784, Images.verifyCode_785, Images.verifyCode_786, Images.verifyCode_787, Images.verifyCode_788, Images.verifyCode_789, Images.verifyCode_790, Images.verifyCode_791, Images.verifyCode_792, Images.verifyCode_793, Images.verifyCode_794, Images.verifyCode_795, Images.verifyCode_796, Images.verifyCode_797, Images.verifyCode_798, Images.verifyCode_799, Images.verifyCode_800, Images.verifyCode_801, Images.verifyCode_802, Images.verifyCode_803, Images.verifyCode_804, Images.verifyCode_805, Images.verifyCode_806, Images.verifyCode_807, Images.verifyCode_808, Images.verifyCode_809, Images.verifyCode_810, Images.verifyCode_811, Images.verifyCode_812, Images.verifyCode_813, Images.verifyCode_814, Images.verifyCode_815, Images.verifyCode_816, Images.verifyCode_817, Images.verifyCode_818, Images.verifyCode_819, Images.verifyCode_820, Images.verifyCode_821]

/-- `verifyCode.drop i`, through the chunks. -/
def lcode (i : Nat) : List (BitVec 32) := ((lChunks.drop (i / 256)).flatten).drop (i % 256)

theorem foldl_append_flatten' : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten' l (a ++ c)]

set_option maxRecDepth 200000 in
theorem lChunks_foldl : Images.verifyCode = lChunks.foldl (· ++ ·) [] := by
  delta Images.verifyCode lChunks
  rfl

theorem lChunks_flatten : Images.verifyCode = lChunks.flatten := by
  rw [lChunks_foldl, foldl_append_flatten', List.nil_append]

set_option maxRecDepth 200000 in
theorem lChunks_ok : (lChunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem lChunks_le : (lChunks.all fun c => decide (c.length ≤ 256)) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem lChunks_length : lChunks.length = 822 := by decide +kernel

theorem drop_chunks' : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this

theorem flatten_len_le' : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le' cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem verifyCode_length_le : Images.verifyCode.length ≤ 256 * 822 := by
  rw [lChunks_flatten, ← lChunks_length]; exact flatten_len_le' _ lChunks_le

theorem lcode_eq (i : Nat) (hi : i / 256 < 822) : lcode i = Images.verifyCode.drop i := by
  unfold lcode
  rw [lChunks_flatten, ← drop_chunks' lChunks (i / 256) lChunks_ok (by rw [lChunks_length]; exact hi),
    List.drop_drop]
  congr 1; omega

/-- `lcode i` sits at `pcOf i` in the verify image. -/
theorem lcodeAt (i : Nat) (hi : i < 210432) : CodeAt Images.verifyImage (pcOf i) (lcode i) := by
  have hl := verifyCode_length_le
  have hp : (pcOf i).toNat = 0x1000 + 4 * i := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  rw [lcode_eq i (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; omega
  · rw [hp]; omega
  · rw [hp, List.length_drop]; omega
  · rw [hp, show (0x1000 + 4 * i - 0x1000) / 4 = i by omega]
    exact List.prefix_refl _

/-! ## Boolean comparison of executor results -/

def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false

theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]

def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields

theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl

def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2

theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]

def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl

theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]

def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles

theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]

/-- `o = some r`, as a Boolean check. -/
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false

theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]

/-- The executor on the image words from instruction `p` (at most `f` instructions). -/
def vrun (p f : Nat) : Option Result := symRun {} (lcode p) (pcOf p) f

/-! ## Label tables (word indices of `t3m/images/verify.labels`) -/

/-- `ctab` (checksum chain dispatch, 9 slots of 8 words). -/
def ctabIdx : Nat := 111104
/-- `ttab` (lower triple table, 512 rows of 16 slots of 8 words). -/
def ttabIdx : Nat := 111176
/-- `q48tab` (chain 48 of the top, 4 slots). -/
def q48tabIdx : Nat := 176712
/-- `qtab` (top quad table, 256 rows of 16 slots of 8 words). -/
def qtabIdx : Nat := 176744
def ckR0 : Nat := 82059
def ckDone : Nat := 82074
def q48R0 : Nat := 110683
def q48Done : Nat := 110690

/-- `tc_t_dB_dC_r0` at `64 t + 8 dB + dC`. -/
def triBaseTab : List Nat :=
  [42027, 42086, 42143, 42198, 42251, 42302, 42351, 42398, 42442, 42499, 42554, 42607, 42658, 42707, 42754, 42799,
  42841, 42896, 42949, 43000, 43049, 43096, 43141, 43184, 43224, 43277, 43328, 43377, 43424, 43469, 43512, 43553,
  43591, 43642, 43691, 43738, 43783, 43826, 43867, 43906, 43942, 43991, 44038, 44083, 44126, 44167, 44206, 44243,
  44277, 44324, 44369, 44412, 44453, 44492, 44529, 44564, 44596, 44640, 44682, 44722, 44760, 44796, 44830, 44862,
  44891, 44950, 45007, 45062, 45115, 45166, 45215, 45262, 45306, 45363, 45418, 45471, 45522, 45571, 45618, 45663,
  45705, 45760, 45813, 45864, 45913, 45960, 46005, 46048, 46088, 46141, 46192, 46241, 46288, 46333, 46376, 46417,
  46455, 46506, 46555, 46602, 46647, 46690, 46731, 46770, 46806, 46855, 46902, 46947, 46990, 47031, 47070, 47107,
  47141, 47188, 47233, 47276, 47317, 47356, 47393, 47428, 47460, 47504, 47546, 47586, 47624, 47660, 47694, 47726,
  47755, 47814, 47871, 47926, 47979, 48030, 48079, 48126, 48170, 48227, 48282, 48335, 48386, 48435, 48482, 48527,
  48569, 48624, 48677, 48728, 48777, 48824, 48869, 48912, 48952, 49005, 49056, 49105, 49152, 49197, 49240, 49281,
  49319, 49370, 49419, 49466, 49511, 49554, 49595, 49634, 49670, 49719, 49766, 49811, 49854, 49895, 49934, 49971,
  50005, 50052, 50097, 50140, 50181, 50220, 50257, 50292, 50324, 50368, 50410, 50450, 50488, 50524, 50558, 50590,
  50619, 50678, 50735, 50790, 50843, 50894, 50943, 50990, 51034, 51091, 51146, 51199, 51250, 51299, 51346, 51391,
  51433, 51488, 51541, 51592, 51641, 51688, 51733, 51776, 51816, 51869, 51920, 51969, 52016, 52061, 52104, 52145,
  52183, 52234, 52283, 52330, 52375, 52418, 52459, 52498, 52534, 52583, 52630, 52675, 52718, 52759, 52798, 52835,
  52869, 52916, 52961, 53004, 53045, 53084, 53121, 53156, 53188, 53232, 53274, 53314, 53352, 53388, 53422, 53454,
  53483, 53542, 53599, 53654, 53707, 53758, 53807, 53854, 53898, 53955, 54010, 54063, 54114, 54163, 54210, 54255,
  54297, 54352, 54405, 54456, 54505, 54552, 54597, 54640, 54680, 54733, 54784, 54833, 54880, 54925, 54968, 55009,
  55047, 55098, 55147, 55194, 55239, 55282, 55323, 55362, 55398, 55447, 55494, 55539, 55582, 55623, 55662, 55699,
  55733, 55780, 55825, 55868, 55909, 55948, 55985, 56020, 56052, 56096, 56138, 56178, 56216, 56252, 56286, 56318,
  56347, 56406, 56463, 56518, 56571, 56622, 56671, 56718, 56762, 56819, 56874, 56927, 56978, 57027, 57074, 57119,
  57161, 57216, 57269, 57320, 57369, 57416, 57461, 57504, 57544, 57597, 57648, 57697, 57744, 57789, 57832, 57873,
  57911, 57962, 58011, 58058, 58103, 58146, 58187, 58226, 58262, 58311, 58358, 58403, 58446, 58487, 58526, 58563,
  58597, 58644, 58689, 58732, 58773, 58812, 58849, 58884, 58916, 58960, 59002, 59042, 59080, 59116, 59150, 59182,
  59211, 59270, 59327, 59382, 59435, 59486, 59535, 59582, 59626, 59683, 59738, 59791, 59842, 59891, 59938, 59983,
  60025, 60080, 60133, 60184, 60233, 60280, 60325, 60368, 60408, 60461, 60512, 60561, 60608, 60653, 60696, 60737,
  60775, 60826, 60875, 60922, 60967, 61010, 61051, 61090, 61126, 61175, 61222, 61267, 61310, 61351, 61390, 61427,
  61461, 61508, 61553, 61596, 61637, 61676, 61713, 61748, 61780, 61824, 61866, 61906, 61944, 61980, 62014, 62046,
  62075, 62134, 62191, 62246, 62299, 62350, 62399, 62446, 62490, 62547, 62602, 62655, 62706, 62755, 62802, 62847,
  62889, 62944, 62997, 63048, 63097, 63144, 63189, 63232, 63272, 63325, 63376, 63425, 63472, 63517, 63560, 63601,
  63639, 63690, 63739, 63786, 63831, 63874, 63915, 63954, 63990, 64039, 64086, 64131, 64174, 64215, 64254, 64291,
  64325, 64372, 64417, 64460, 64501, 64540, 64577, 64612, 64644, 64688, 64730, 64770, 64808, 64844, 64878, 64910,
  64939, 64998, 65055, 65110, 65163, 65214, 65263, 65310, 65354, 65411, 65466, 65519, 65570, 65619, 65666, 65711,
  65753, 65808, 65861, 65912, 65961, 66008, 66053, 66096, 66136, 66189, 66240, 66289, 66336, 66381, 66424, 66465,
  66503, 66554, 66603, 66650, 66695, 66738, 66779, 66818, 66854, 66903, 66950, 66995, 67038, 67079, 67118, 67155,
  67189, 67236, 67281, 67324, 67365, 67404, 67441, 67476, 67508, 67552, 67594, 67634, 67672, 67708, 67742, 67774,
  67803, 67862, 67919, 67974, 68027, 68078, 68127, 68174, 68218, 68275, 68330, 68383, 68434, 68483, 68530, 68575,
  68617, 68672, 68725, 68776, 68825, 68872, 68917, 68960, 69000, 69053, 69104, 69153, 69200, 69245, 69288, 69329,
  69367, 69418, 69467, 69514, 69559, 69602, 69643, 69682, 69718, 69767, 69814, 69859, 69902, 69943, 69982, 70019,
  70053, 70100, 70145, 70188, 70229, 70268, 70305, 70340, 70372, 70416, 70458, 70498, 70536, 70572, 70606, 70638,
  70667, 70726, 70783, 70838, 70891, 70942, 70991, 71038, 71082, 71139, 71194, 71247, 71298, 71347, 71394, 71439,
  71481, 71536, 71589, 71640, 71689, 71736, 71781, 71824, 71864, 71917, 71968, 72017, 72064, 72109, 72152, 72193,
  72231, 72282, 72331, 72378, 72423, 72466, 72507, 72546, 72582, 72631, 72678, 72723, 72766, 72807, 72846, 72883,
  72917, 72964, 73009, 73052, 73093, 73132, 73169, 73204, 73236, 73280, 73322, 73362, 73400, 73436, 73470, 73502,
  73531, 73590, 73647, 73702, 73755, 73806, 73855, 73902, 73946, 74003, 74058, 74111, 74162, 74211, 74258, 74303,
  74345, 74400, 74453, 74504, 74553, 74600, 74645, 74688, 74728, 74781, 74832, 74881, 74928, 74973, 75016, 75057,
  75095, 75146, 75195, 75242, 75287, 75330, 75371, 75410, 75446, 75495, 75542, 75587, 75630, 75671, 75710, 75747,
  75781, 75828, 75873, 75916, 75957, 75996, 76033, 76068, 76100, 76144, 76186, 76226, 76264, 76300, 76334, 76366,
  76395, 76454, 76511, 76566, 76619, 76670, 76719, 76766, 76810, 76867, 76922, 76975, 77026, 77075, 77122, 77167,
  77209, 77264, 77317, 77368, 77417, 77464, 77509, 77552, 77592, 77645, 77696, 77745, 77792, 77837, 77880, 77921,
  77959, 78010, 78059, 78106, 78151, 78194, 78235, 78274, 78310, 78359, 78406, 78451, 78494, 78535, 78574, 78611,
  78645, 78692, 78737, 78780, 78821, 78860, 78897, 78932, 78964, 79008, 79050, 79090, 79128, 79164, 79198, 79230,
  79259, 79317, 79373, 79427, 79479, 79529, 79577, 79623, 79666, 79722, 79776, 79828, 79878, 79926, 79972, 80016,
  80057, 80111, 80163, 80213, 80261, 80307, 80351, 80393, 80432, 80484, 80534, 80582, 80628, 80672, 80714, 80754,
  80791, 80841, 80889, 80935, 80979, 81021, 81061, 81099, 81134, 81182, 81228, 81272, 81314, 81354, 81392, 81428,
  81461, 81507, 81551, 81593, 81633, 81671, 81707, 81741, 81772, 81815, 81856, 81895, 81932, 81967, 82000, 82031]

/-- `tq_q_dB_dC_dD_r0` at `64 q + 16 dB + 4 dC + dD`. -/
def quadBaseTab : List Nat :=
  [82075, 82122, 82167, 82210, 82250, 82295, 82338, 82379, 82417, 82460, 82501, 82540, 82576, 82616, 82654, 82690,
  82723, 82768, 82811, 82852, 82890, 82933, 82974, 83013, 83049, 83090, 83129, 83166, 83200, 83238, 83274, 83308,
  83339, 83382, 83423, 83462, 83498, 83539, 83578, 83615, 83649, 83688, 83725, 83760, 83792, 83828, 83862, 83894,
  83923, 83963, 84001, 84037, 84070, 84108, 84144, 84178, 84209, 84245, 84279, 84311, 84340, 84373, 84404, 84433,
  84459, 84506, 84551, 84594, 84634, 84679, 84722, 84763, 84801, 84844, 84885, 84924, 84960, 85000, 85038, 85074,
  85107, 85152, 85195, 85236, 85274, 85317, 85358, 85397, 85433, 85474, 85513, 85550, 85584, 85622, 85658, 85692,
  85723, 85766, 85807, 85846, 85882, 85923, 85962, 85999, 86033, 86072, 86109, 86144, 86176, 86212, 86246, 86278,
  86307, 86347, 86385, 86421, 86454, 86492, 86528, 86562, 86593, 86629, 86663, 86695, 86724, 86757, 86788, 86817,
  86843, 86890, 86935, 86978, 87018, 87063, 87106, 87147, 87185, 87228, 87269, 87308, 87344, 87384, 87422, 87458,
  87491, 87536, 87579, 87620, 87658, 87701, 87742, 87781, 87817, 87858, 87897, 87934, 87968, 88006, 88042, 88076,
  88107, 88150, 88191, 88230, 88266, 88307, 88346, 88383, 88417, 88456, 88493, 88528, 88560, 88596, 88630, 88662,
  88691, 88731, 88769, 88805, 88838, 88876, 88912, 88946, 88977, 89013, 89047, 89079, 89108, 89141, 89172, 89201,
  89227, 89274, 89319, 89362, 89402, 89447, 89490, 89531, 89569, 89612, 89653, 89692, 89728, 89768, 89806, 89842,
  89875, 89920, 89963, 90004, 90042, 90085, 90126, 90165, 90201, 90242, 90281, 90318, 90352, 90390, 90426, 90460,
  90491, 90534, 90575, 90614, 90650, 90691, 90730, 90767, 90801, 90840, 90877, 90912, 90944, 90980, 91014, 91046,
  91075, 91115, 91153, 91189, 91222, 91260, 91296, 91330, 91361, 91397, 91431, 91463, 91492, 91525, 91556, 91585,
  91611, 91658, 91703, 91746, 91786, 91831, 91874, 91915, 91953, 91996, 92037, 92076, 92112, 92152, 92190, 92226,
  92259, 92304, 92347, 92388, 92426, 92469, 92510, 92549, 92585, 92626, 92665, 92702, 92736, 92774, 92810, 92844,
  92875, 92918, 92959, 92998, 93034, 93075, 93114, 93151, 93185, 93224, 93261, 93296, 93328, 93364, 93398, 93430,
  93459, 93499, 93537, 93573, 93606, 93644, 93680, 93714, 93745, 93781, 93815, 93847, 93876, 93909, 93940, 93969,
  93995, 94042, 94087, 94130, 94170, 94215, 94258, 94299, 94337, 94380, 94421, 94460, 94496, 94536, 94574, 94610,
  94643, 94688, 94731, 94772, 94810, 94853, 94894, 94933, 94969, 95010, 95049, 95086, 95120, 95158, 95194, 95228,
  95259, 95302, 95343, 95382, 95418, 95459, 95498, 95535, 95569, 95608, 95645, 95680, 95712, 95748, 95782, 95814,
  95843, 95883, 95921, 95957, 95990, 96028, 96064, 96098, 96129, 96165, 96199, 96231, 96260, 96293, 96324, 96353,
  96379, 96426, 96471, 96514, 96554, 96599, 96642, 96683, 96721, 96764, 96805, 96844, 96880, 96920, 96958, 96994,
  97027, 97072, 97115, 97156, 97194, 97237, 97278, 97317, 97353, 97394, 97433, 97470, 97504, 97542, 97578, 97612,
  97643, 97686, 97727, 97766, 97802, 97843, 97882, 97919, 97953, 97992, 98029, 98064, 98096, 98132, 98166, 98198,
  98227, 98267, 98305, 98341, 98374, 98412, 98448, 98482, 98513, 98549, 98583, 98615, 98644, 98677, 98708, 98737,
  98763, 98810, 98855, 98898, 98938, 98983, 99026, 99067, 99105, 99148, 99189, 99228, 99264, 99304, 99342, 99378,
  99411, 99456, 99499, 99540, 99578, 99621, 99662, 99701, 99737, 99778, 99817, 99854, 99888, 99926, 99962, 99996,
  100027, 100070, 100111, 100150, 100186, 100227, 100266, 100303, 100337, 100376, 100413, 100448, 100480, 100516, 100550, 100582,
  100611, 100651, 100689, 100725, 100758, 100796, 100832, 100866, 100897, 100933, 100967, 100999, 101028, 101061, 101092, 101121,
  101147, 101194, 101239, 101282, 101322, 101367, 101410, 101451, 101489, 101532, 101573, 101612, 101648, 101688, 101726, 101762,
  101795, 101840, 101883, 101924, 101962, 102005, 102046, 102085, 102121, 102162, 102201, 102238, 102272, 102310, 102346, 102380,
  102411, 102454, 102495, 102534, 102570, 102611, 102650, 102687, 102721, 102760, 102797, 102832, 102864, 102900, 102934, 102966,
  102995, 103035, 103073, 103109, 103142, 103180, 103216, 103250, 103281, 103317, 103351, 103383, 103412, 103445, 103476, 103505,
  103531, 103578, 103623, 103666, 103706, 103751, 103794, 103835, 103873, 103916, 103957, 103996, 104032, 104072, 104110, 104146,
  104179, 104224, 104267, 104308, 104346, 104389, 104430, 104469, 104505, 104546, 104585, 104622, 104656, 104694, 104730, 104764,
  104795, 104838, 104879, 104918, 104954, 104995, 105034, 105071, 105105, 105144, 105181, 105216, 105248, 105284, 105318, 105350,
  105379, 105419, 105457, 105493, 105526, 105564, 105600, 105634, 105665, 105701, 105735, 105767, 105796, 105829, 105860, 105889,
  105915, 105962, 106007, 106050, 106090, 106135, 106178, 106219, 106257, 106300, 106341, 106380, 106416, 106456, 106494, 106530,
  106563, 106608, 106651, 106692, 106730, 106773, 106814, 106853, 106889, 106930, 106969, 107006, 107040, 107078, 107114, 107148,
  107179, 107222, 107263, 107302, 107338, 107379, 107418, 107455, 107489, 107528, 107565, 107600, 107632, 107668, 107702, 107734,
  107763, 107803, 107841, 107877, 107910, 107948, 107984, 108018, 108049, 108085, 108119, 108151, 108180, 108213, 108244, 108273,
  108299, 108346, 108391, 108434, 108474, 108519, 108562, 108603, 108641, 108684, 108725, 108764, 108800, 108840, 108878, 108914,
  108947, 108992, 109035, 109076, 109114, 109157, 109198, 109237, 109273, 109314, 109353, 109390, 109424, 109462, 109498, 109532,
  109563, 109606, 109647, 109686, 109722, 109763, 109802, 109839, 109873, 109912, 109949, 109984, 110016, 110052, 110086, 110118,
  110147, 110187, 110225, 110261, 110294, 110332, 110368, 110402, 110433, 110469, 110503, 110535, 110564, 110597, 110628, 110657]

/-! ## Expected results -/

/-- The registers holding the step bytes `0 .. 6`: `zero, t1, t2, s0, s1, a3, s10`. -/
def posReg (d : Nat) : Reg :=
  match d with
  | 0 => .x0 | 1 => .x6 | 2 => .x7 | 3 => .x8 | 4 => .x9 | 5 => .x13 | _ => .x26

/-- The step byte as the executor reads it (`zero` is the constant 0). -/
def posE (d : Nat) : E := RegFile.init.get (posReg d)

/-- The running chain header word: `s9 + t3` (the chain index byte 5 bumped). -/
def bumpE : E := .bin .add (.reg .x25) (.reg .x28)
/-- `mv s9, s11` (the first chain of a layer) or the bump. -/
def s9E (first : Bool) : E := if first then .reg .x27 else bumpE

/-- The doubleword key `base + off + k`. -/
def kAt (rb : Reg) (off : Word) (k : Nat) : Addr := ⟨some (.reg rb), off + BitVec.ofNat 64 k⟩
/-- The initial memory word at `base + off + k`. -/
def lAt (rb : Reg) (off : Word) (k : Nat) : E := .ld (addC (.reg rb) (off + BitVec.ofNat 64 k))

/-- A chain head in a table slot: `addi a0, base, off; addi a2, a0, 48; s9 := …; sd s9, 16(a0); sd tp, 24(a0)`,
then `j tgt` (6 steps). -/
def headJ (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (addC (.reg rb) off) 48)).set .x25 (s9E first),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, s9E first)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩, .c (pcOf tgt), .jump, 6, 6⟩

/-- An inline chain head (with the bump) and its first rung, step `d` (`slot` = the leaf-pk slot when `d` is
the last step), up to the rung's `ecall` (6 or 7 steps from `p`). -/
def headR (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 7 else 6
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 bumpE,
    [(kAt rb off 16, .bin (.st .b 4) bumpE (posE d)), (kAt rb off 24, .reg .x4)],
    [.align8 (.reg rb), .valid (kAt rb off 20) 1, .valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

/-- A rung at `p`: `sb POS_d, 20(a0)`, `[li a2, slot]`, up to the `ecall` (1 or 2 steps). -/
def rungR (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 2 else 1
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 4) (.ld (addC (.reg .x10) 16)) (posE d))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 20⟩ 1]⟩, .c (pcOf (p + n)), .ecall, n, n⟩

/-- The registers after a max-digit copy (`gp`, `a4` = the two value words). -/
def copyRegs (rb : Reg) (off : Word) : RegFile :=
  (RegFile.init.set .x3 (lAt rb off 48)).set .x14 (lAt rb off 56)

/-- The copy's stores into the leaf-pk slot. -/
def copyMem (rb : Reg) (off : Word) (slot : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (slot + 8)⟩, lAt rb off 56), (⟨none, BitVec.ofNat 64 slot⟩, lAt rb off 48)]

def copyObl (rb : Reg) (off : Word) : List Oblig := [.valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]

/-- A max-digit copy in a table slot (with `s9 := …`), then `j tgt` (6 steps). -/
def copyJ (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 (s9E first), copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 6, 6⟩

/-- An inline max-digit copy (with the bump), stopped after its 5 instructions. -/
def copyF (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 bumpE, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 5)), .fuel, 5, 5⟩

/-- The checksum chain's copy (no `s9` update), then `j tgt` (5 steps). -/
def copyN (rb : Reg) (off : Word) (slot : Nat) (tgt : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 5, 5⟩

/-! ### T3X: the lower chain code's heads read the WOTS header table

(erickeigen 59cbf8ec's design, lower layers only.) During a lower layer's chain phase `x28` holds the midpoint of
the layer's 4096-byte header bank (`Verify.headerBank`); a head loads its chain/digit header word with one `ld`
instead of the running `s9` bump and the first step's byte store. A table-slot max-digit copy is then `copyN`.
The top layer's chain code (`Nonbinary`) keeps `headJ` / `headR` / `copyJ` / `copyF` above. -/

/-- Byte offset of the header of chain `i`, digit `d` from the bank midpoint. -/
def hOff (i d : Nat) : Word := BitVec.ofNat 64 (64 * i + 8 * d) - 2048

def hKey (i d : Nat) : Addr := ⟨some (.reg .x28), hOff i d⟩
def hLoad (i d : Nat) : E := .ld (addC (.reg .x28) (hOff i d))

/-- A table-slot head: `addi a0, base, off; addi a2, a0, 48; ld s9, hOff i 0(t3); sd s9, 16(a0); sd tp, 24(a0)`,
then `j tgt` (6 steps). -/
def headJH (rb : Reg) (off : Word) (tgt i : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (addC (.reg rb) off) 48)).set .x25 (hLoad i 0),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, hLoad i 0)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8, .valid (hKey i 0) 8]⟩,
    .c (pcOf tgt), .jump, 6, 6⟩

/-- An inline head loading the header with its first digit `d` already set (no byte store), up to the first
`ecall` (5 or 6 steps from `p`). -/
def headRH (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  let n := if slot.isSome then 6 else 5
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, hLoad i d)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8, .valid (hKey i d) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

/-- An inline max-digit copy without the bump, stopped after its 4 instructions. -/
def copyFH (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩

/-- `slli/srli/mv a4, w, ·`: bit `b` of `w` to bit 9. -/
def shE (w : Reg) (b : Nat) : E :=
  if b < 9 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (9 - b)))
  else if 9 < b then .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b - 9)))
  else .reg w

/-- The dispatch into a table slot: `a4 = (shE w b &&& mreg) + a5`, `jalr zero, imm(a4)` (4 steps). -/
def xJ (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)), [], []⟩,
    .bin .and (.bin .add (.bin .add (.bin .and (shE w b) (.reg mreg)) (.reg .x15)) (.c imm)) (.c (~~~1#64)),
    .jump, (if b = 9 then 3 else 4), (if b = 9 then 3 else 4)⟩

/-- After triple 13: `slli a4, t4, 5; sub a4, a5, a4; jalr zero, -1824(a4)` into `ctab` (3 steps; `t4 = 7 - ck`). -/
def ctabX : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 5))), [], []⟩,
    .bin .and (.bin .add (.bin .sub (.reg .x15) (.bin .sll (.reg .x29) (.c 5))) (.c (-1824))) (.c (~~~1#64)),
    .jump, 3, 3⟩

/-- After quad 11: `srli a4, a7, 29; andi a4, a4, 0x60; add a4, a4, a5; jalr zero, -1760(a4)` into `q48tab`. -/
def q48X : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 29)) (.c 0x60)) (.reg .x15)), [], []⟩,
    .bin .and (.bin .add (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 29)) (.c 0x60)) (.reg .x15)) (.c (-1760)))
      (.c (~~~1#64)), .jump, 4, 4⟩

/-- `q48_done`: `lui a5, 0x6e; srli a4, a7, 27; and a4, a4, sp; add a4, a4, a5; jalr zero, -1408(a4)` into the
lower table's slot 11 (5 steps). -/
def q48D : Result :=
  ⟨⟨(RegFile.init.set .x15 (.c 0x6e000)).set .x14
      (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 27)) (.reg .x2)) (.c 0x6e000)), [], []⟩,
    .bin .and (.bin .add (.bin .and (.bin .srl (.reg .x17) (.c 27)) (.reg .x2)) (.c (0x6e000 - 1408)))
      (.c (~~~1#64)), .jump, 5, 5⟩

/-- `jr ra` (1 step). -/
def retR : Result := ⟨⟨RegFile.init, [], []⟩, .bin .and (.reg .x1) (.c (~~~1#64)), .jump, 1, 1⟩

/-! ## The lower chain code (triples, checksum) -/

/-- Chain block `i` of a lower layer relative to `s6 = x22`: `64 (42 - i) - 1024`. -/
def offL (i : Nat) : Word := BitVec.ofNat 64 (64 * (42 - i)) - BitVec.ofNat 64 1024
/-- The lower leaf-pk slot of chain `i` (`0x300` for chain 0, `0x310 + 16 i` else). -/
def slotL (i : Nat) : Nat := if i = 0 then 768 else 784 + 16 * i

def triBase (t dB dC : Nat) : Nat := triBaseTab.getD (64 * t + 8 * dB + dC) 0
/-- Words of an inline chain at digit `d` (width 3): the copy 4, else the head 4 + rungs `2 (7 - d) + 1` (T3X:
the header `ld` replaces the bump and the first byte store). -/
def partLen (d : Nat) : Nat := if d = 7 then 4 else 19 - 2 * d
def pcB (t dB dC : Nat) : Nat := triBase t dB dC + 15
def pcC (t dB dC : Nat) : Nat := pcB t dB dC + partLen dB
def pcX (t dB dC : Nat) : Nat := pcC t dB dC + partLen dC
/-- Slot `t` of row `k` of `ttab`. -/
def entW (t k : Nat) : Nat := ttabIdx + 128 * k + 8 * t

/-- The rungs `d0 .. 6` (width 3) starting at `p`, the last one into `slot`. -/
def rungsOK (d0 slot p : Nat) : Bool :=
  (List.range' d0 (7 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungR m (if m = 6 then some slot else none) (p + 2 * (m - d0)))

/-- The inline code of lower chain `i` at digit `d`, from `p`. -/
def partOK (i d p : Nat) : Bool :=
  if d = 7 then rOK (vrun p 4) (copyFH .x22 (offL i) (slotL i) p)
  else rOK (vrun p 8) (headRH .x22 (offL i) d (if d = 6 then some (slotL i) else none) p i) &&
    rungsOK (d + 1) (slotL i) (p + 6)

/-- Slot `(t, k)` of `ttab`: chain `3t`'s head into rung `dA` of the shared block, or its copy. -/
def entCheck (t k : Nat) : Bool :=
  if k % 8 = 7 then
    rOK (vrun (entW t k) 7) (copyN .x22 (offL (3 * t)) (slotL (3 * t)) (pcB t (k / 8 % 8) (k / 64)))
  else rOK (vrun (entW t k) 7) (headJH .x22 (offL (3 * t)) (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8)) (3 * t))

/-- After chain `C` of triple `t`: the dispatch of triple `t + 1` or (`t = 13`) of the checksum chain. -/
def xOK (t dB dC : Nat) : Bool :=
  if t = 13 then rOK (vrun (pcX t dB dC) 4) ctabX
  else rOK (vrun (pcX t dB dC) 5)
    (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760))

/-- The shared block `tc_t_dB_dC`: `A`'s rungs, `B`, `C`, the next dispatch. -/
def blkCheck (t dB dC : Nat) : Bool :=
  rungsOK 0 (slotL (3 * t)) (triBase t dB dC) && partOK (3 * t + 1) dB (pcB t dB dC) &&
    partOK (3 * t + 2) dC (pcC t dB dC) && xOK t dB dC

/-- Everything of triple `t`: table rows `lo .. lo + n` and the code blocks `lo / 8 .. (lo + n) / 8`. -/
def triCheck (t lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => entCheck t k) &&
    ((List.range' (lo / 8) (n / 8)).all fun q => blkCheck t (q / 8) (q % 8))

/-- The checksum chain: `ctab` (digit `c < 7` head, `c = 7` copy, slot 8 `jr ra`), its rungs, `ck_done`. -/
def ckCheck : Bool :=
  ((List.range 7).all fun c => rOK (vrun (ctabIdx + 8 * c) 7) (headJH .x22 (offL 42) (ckR0 + 2 * c) 42)) &&
    rOK (vrun (ctabIdx + 56) 6) (copyN .x22 (offL 42) (slotL 42) ckDone) &&
    rOK (vrun (ctabIdx + 64) 2) retR && rungsOK 0 (slotL 42) ckR0 && rOK (vrun ckDone 2) retR

/-! ## The top chain code (quads, chain 48) -/

/-- Chain block `i < 49` of the top relative to `s3 = x19`: `64 (57 - i) - 1664`. -/
def offT (i : Nat) : Word := BitVec.ofNat 64 (64 * (57 - i)) - BitVec.ofNat 64 1664
/-- The top leaf-pk slot of chain `i` (`0x200` for chain 0, `0x210 + 16 i` else). -/
def slotT (i : Nat) : Nat := if i = 0 then 512 else 528 + 16 * i

def quadBase (q dB dC dD : Nat) : Nat := quadBaseTab.getD (64 * q + 16 * dB + 4 * dC + dD) 0
/-- Words of an inline chain at digit `d` (width 2): the copy 5, else the head 5 + rungs `2 (3 - d) + 1`. -/
def partLen2 (d : Nat) : Nat := if d = 3 then 5 else 12 - 2 * d
def qpcB (q dB dC dD : Nat) : Nat := quadBase q dB dC dD + 7
def qpcC (q dB dC dD : Nat) : Nat := qpcB q dB dC dD + partLen2 dB
def qpcD (q dB dC dD : Nat) : Nat := qpcC q dB dC dD + partLen2 dC
def qpcX (q dB dC dD : Nat) : Nat := qpcD q dB dC dD + partLen2 dD
/-- Slot `q` of row `k` of `qtab`. -/
def qentW (q k : Nat) : Nat := qtabIdx + 128 * k + 8 * q

/-- The rungs `d0 .. 2` (width 2) starting at `p`, the last one into `slot`. -/
def rungsOK2 (d0 slot p : Nat) : Bool :=
  (List.range' d0 (3 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungR m (if m = 2 then some slot else none) (p + 2 * (m - d0)))

/-- The inline code of top chain `i < 49` at digit `d`, from `p`. -/
def partOK2 (i d p : Nat) : Bool :=
  if d = 3 then rOK (vrun p 5) (copyF .x19 (offT i) (slotT i) p)
  else rOK (vrun p 8) (headR .x19 (offT i) d (if d = 2 then some (slotT i) else none) p) &&
    rungsOK2 (d + 1) (slotT i) (p + 7)

/-- Slot `(q, k)` of `qtab`: chain `4q`'s head into rung `dA` of the shared block, or its copy. -/
def qentCheck (q k : Nat) : Bool :=
  if k % 4 = 3 then
    rOK (vrun (qentW q k) 7)
      (copyJ .x19 (offT (4 * q)) (slotT (4 * q)) (q == 0) (qpcB q (k / 4 % 4) (k / 16 % 4) (k / 64)))
  else rOK (vrun (qentW q k) 7)
    (headJ .x19 (offT (4 * q)) (q == 0) (quadBase q (k / 4 % 4) (k / 16 % 4) (k / 64) + 2 * (k % 4)))

/-- After chain `D` of quad `q`: the dispatch of quad `q + 1` or (`q = 11`) of chain 48. -/
def qxOK (q dB dC dD : Nat) : Bool :=
  if q = 11 then rOK (vrun (qpcX q dB dC dD) 5) q48X
  else rOK (vrun (qpcX q dB dC dD) 5)
    (xJ (if q + 1 < 8 then .x16 else .x17) (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) .x24
      (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632))

/-- The shared block `tq_q_dB_dC_dD`: `A`'s rungs, `B`, `C`, `D`, the next dispatch. -/
def qblkCheck (q dB dC dD : Nat) : Bool :=
  rungsOK2 0 (slotT (4 * q)) (quadBase q dB dC dD) && partOK2 (4 * q + 1) dB (qpcB q dB dC dD) &&
    partOK2 (4 * q + 2) dC (qpcC q dB dC dD) && partOK2 (4 * q + 3) dD (qpcD q dB dC dD) && qxOK q dB dC dD

/-- Everything of quad `q`: table rows `lo .. lo + n` and the code blocks `lo / 4 .. (lo + n) / 4`. -/
def quadCheck (q lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => qentCheck q k) &&
    ((List.range' (lo / 4) (n / 4)).all fun x => qblkCheck q (x / 16) (x / 4 % 4) (x % 4))

/-- Chain 48 of the top: `q48tab` (digit `< 3` head, 3 copy), its rungs, `q48_done`. -/
def q48Check : Bool :=
  ((List.range 3).all fun d => rOK (vrun (q48tabIdx + 8 * d) 7) (headJ .x19 (offT 48) false (q48R0 + 2 * d))) &&
    rOK (vrun (q48tabIdx + 24) 7) (copyJ .x19 (offT 48) (slotT 48) false q48Done) &&
    rungsOK2 0 (slotT 48) q48R0 && rOK (vrun q48Done 6) q48D

end SigGolfCandidate.T3M
