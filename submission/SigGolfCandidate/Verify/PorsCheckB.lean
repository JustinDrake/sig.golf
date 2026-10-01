import SigGolfCandidate.Verify.PorsCheckA
set_option Elab.async false
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
theorem startCheck_ok : startCheck = true := by decide +kernel
theorem leafCheck_all : (List.range 15).all leafCheck = true := by decide +kernel
theorem pentCheck_ok : pentCheck = true := by decide +kernel
theorem posCheck_0 : posCheck 0 = true := by decide +kernel
theorem posCheck_1 : posCheck 1 = true := by decide +kernel
theorem posCheck_2 : posCheck 2 = true := by decide +kernel
theorem prefixCheck_0 : prefixCheck 0 = true := by decide +kernel
theorem prefixCheck_1 : prefixCheck 1 = true := by decide +kernel
theorem prefixCheck_2 : prefixCheck 2 = true := by decide +kernel
theorem tailFCheck_all : (List.range 3).all tailFCheck = true := by decide +kernel
private theorem disp_0 : dispCheck 0 = true := by decide +kernel
private theorem disp_1 : dispCheck 1 = true := by decide +kernel
private theorem disp_2 : dispCheck 2 = true := by decide +kernel
private theorem disp_3 : dispCheck 3 = true := by decide +kernel
private theorem disp_4 : dispCheck 4 = true := by decide +kernel
private theorem disp_5 : dispCheck 5 = true := by decide +kernel
private theorem disp_6 : dispCheck 6 = true := by decide +kernel
private theorem disp_7 : dispCheck 7 = true := by decide +kernel
private theorem disp_8 : dispCheck 8 = true := by decide +kernel
private theorem disp_9 : dispCheck 9 = true := by decide +kernel
private theorem disp_10 : dispCheck 10 = true := by decide +kernel
private theorem disp_11 : dispCheck 11 = true := by decide +kernel
private theorem disp_12 : dispCheck 12 = true := by decide +kernel
private theorem disp_13 : dispCheck 13 = true := by decide +kernel
private theorem disp_14 : dispCheck 14 = true := by decide +kernel
private theorem disp_15 : dispCheck 15 = true := by decide +kernel
private theorem disp_16 : dispCheck 16 = true := by decide +kernel
private theorem disp_17 : dispCheck 17 = true := by decide +kernel
private theorem disp_18 : dispCheck 18 = true := by decide +kernel
private theorem disp_19 : dispCheck 19 = true := by decide +kernel
private theorem disp_20 : dispCheck 20 = true := by decide +kernel
private theorem disp_21 : dispCheck 21 = true := by decide +kernel
private theorem disp_22 : dispCheck 22 = true := by decide +kernel
private theorem disp_23 : dispCheck 23 = true := by decide +kernel
private theorem disp_24 : dispCheck 24 = true := by decide +kernel
private theorem disp_25 : dispCheck 25 = true := by decide +kernel
private theorem disp_26 : dispCheck 26 = true := by decide +kernel
private theorem disp_27 : dispCheck 27 = true := by decide +kernel
private theorem disp_28 : dispCheck 28 = true := by decide +kernel
private theorem disp_29 : dispCheck 29 = true := by decide +kernel
private theorem disp_30 : dispCheck 30 = true := by decide +kernel
private theorem disp_31 : dispCheck 31 = true := by decide +kernel
private theorem disp_32 : dispCheck 32 = true := by decide +kernel
private theorem disp_33 : dispCheck 33 = true := by decide +kernel
private theorem disp_34 : dispCheck 34 = true := by decide +kernel
private theorem disp_35 : dispCheck 35 = true := by decide +kernel
private theorem disp_36 : dispCheck 36 = true := by decide +kernel
private theorem disp_37 : dispCheck 37 = true := by decide +kernel
private theorem disp_38 : dispCheck 38 = true := by decide +kernel
private theorem disp_39 : dispCheck 39 = true := by decide +kernel
private theorem disp_40 : dispCheck 40 = true := by decide +kernel
private theorem disp_41 : dispCheck 41 = true := by decide +kernel
private theorem disp_42 : dispCheck 42 = true := by decide +kernel
private theorem disp_43 : dispCheck 43 = true := by decide +kernel
private theorem disp_44 : dispCheck 44 = true := by decide +kernel
private theorem disp_45 : dispCheck 45 = true := by decide +kernel
private theorem disp_46 : dispCheck 46 = true := by decide +kernel
private theorem disp_47 : dispCheck 47 = true := by decide +kernel
private theorem disp_48 : dispCheck 48 = true := by decide +kernel
private theorem disp_49 : dispCheck 49 = true := by decide +kernel
private theorem disp_50 : dispCheck 50 = true := by decide +kernel
private theorem disp_51 : dispCheck 51 = true := by decide +kernel
private theorem disp_52 : dispCheck 52 = true := by decide +kernel
private theorem disp_53 : dispCheck 53 = true := by decide +kernel
private theorem disp_54 : dispCheck 54 = true := by decide +kernel
private theorem disp_55 : dispCheck 55 = true := by decide +kernel
private theorem disp_56 : dispCheck 56 = true := by decide +kernel
private theorem disp_57 : dispCheck 57 = true := by decide +kernel
private theorem disp_58 : dispCheck 58 = true := by decide +kernel
private theorem disp_59 : dispCheck 59 = true := by decide +kernel
private theorem disp_60 : dispCheck 60 = true := by decide +kernel
private theorem disp_61 : dispCheck 61 = true := by decide +kernel
private theorem disp_62 : dispCheck 62 = true := by decide +kernel
private theorem disp_63 : dispCheck 63 = true := by decide +kernel
private theorem disp_64 : dispCheck 64 = true := by decide +kernel
private theorem disp_65 : dispCheck 65 = true := by decide +kernel
private theorem disp_66 : dispCheck 66 = true := by decide +kernel
private theorem disp_67 : dispCheck 67 = true := by decide +kernel
private theorem disp_68 : dispCheck 68 = true := by decide +kernel
private theorem disp_69 : dispCheck 69 = true := by decide +kernel
private theorem disp_70 : dispCheck 70 = true := by decide +kernel
private theorem disp_71 : dispCheck 71 = true := by decide +kernel
private theorem disp_72 : dispCheck 72 = true := by decide +kernel
private theorem disp_73 : dispCheck 73 = true := by decide +kernel
private theorem disp_74 : dispCheck 74 = true := by decide +kernel
private theorem disp_75 : dispCheck 75 = true := by decide +kernel
private theorem disp_76 : dispCheck 76 = true := by decide +kernel
private theorem disp_77 : dispCheck 77 = true := by decide +kernel
private theorem disp_78 : dispCheck 78 = true := by decide +kernel
private theorem disp_79 : dispCheck 79 = true := by decide +kernel
private theorem disp_80 : dispCheck 80 = true := by decide +kernel
private theorem disp_81 : dispCheck 81 = true := by decide +kernel
private theorem disp_82 : dispCheck 82 = true := by decide +kernel
private theorem disp_83 : dispCheck 83 = true := by decide +kernel
private theorem disp_84 : dispCheck 84 = true := by decide +kernel
private theorem disp_85 : dispCheck 85 = true := by decide +kernel
private theorem disp_86 : dispCheck 86 = true := by decide +kernel
private theorem disp_87 : dispCheck 87 = true := by decide +kernel
private theorem disp_88 : dispCheck 88 = true := by decide +kernel
private theorem disp_89 : dispCheck 89 = true := by decide +kernel
private theorem disp_90 : dispCheck 90 = true := by decide +kernel
private theorem disp_91 : dispCheck 91 = true := by decide +kernel
private theorem disp_92 : dispCheck 92 = true := by decide +kernel
private theorem disp_93 : dispCheck 93 = true := by decide +kernel
private theorem disp_94 : dispCheck 94 = true := by decide +kernel
private theorem disp_95 : dispCheck 95 = true := by decide +kernel
private theorem disp_96 : dispCheck 96 = true := by decide +kernel
private theorem disp_97 : dispCheck 97 = true := by decide +kernel
private theorem disp_98 : dispCheck 98 = true := by decide +kernel
private theorem disp_99 : dispCheck 99 = true := by decide +kernel
private theorem disp_100 : dispCheck 100 = true := by decide +kernel
private theorem disp_101 : dispCheck 101 = true := by decide +kernel
private theorem disp_102 : dispCheck 102 = true := by decide +kernel
private theorem disp_103 : dispCheck 103 = true := by decide +kernel
private theorem disp_104 : dispCheck 104 = true := by decide +kernel
private theorem disp_105 : dispCheck 105 = true := by decide +kernel
private theorem disp_106 : dispCheck 106 = true := by decide +kernel
private theorem disp_107 : dispCheck 107 = true := by decide +kernel
private theorem disp_108 : dispCheck 108 = true := by decide +kernel
private theorem disp_109 : dispCheck 109 = true := by decide +kernel
private theorem disp_110 : dispCheck 110 = true := by decide +kernel
private theorem disp_111 : dispCheck 111 = true := by decide +kernel
private theorem disp_112 : dispCheck 112 = true := by decide +kernel
private theorem disp_113 : dispCheck 113 = true := by decide +kernel
private theorem disp_114 : dispCheck 114 = true := by decide +kernel
private theorem disp_115 : dispCheck 115 = true := by decide +kernel
private theorem disp_116 : dispCheck 116 = true := by decide +kernel
private theorem disp_117 : dispCheck 117 = true := by decide +kernel
private theorem disp_118 : dispCheck 118 = true := by decide +kernel
private theorem disp_119 : dispCheck 119 = true := by decide +kernel
private theorem disp_120 : dispCheck 120 = true := by decide +kernel
private theorem disp_121 : dispCheck 121 = true := by decide +kernel
private theorem disp_122 : dispCheck 122 = true := by decide +kernel
private theorem disp_123 : dispCheck 123 = true := by decide +kernel
private theorem disp_124 : dispCheck 124 = true := by decide +kernel
private theorem disp_125 : dispCheck 125 = true := by decide +kernel
private theorem disp_126 : dispCheck 126 = true := by decide +kernel
private theorem disp_127 : dispCheck 127 = true := by decide +kernel
private theorem disp_128 : dispCheck 128 = true := by decide +kernel
private theorem disp_129 : dispCheck 129 = true := by decide +kernel
private theorem disp_130 : dispCheck 130 = true := by decide +kernel
private theorem disp_131 : dispCheck 131 = true := by decide +kernel
private theorem disp_132 : dispCheck 132 = true := by decide +kernel
private theorem disp_133 : dispCheck 133 = true := by decide +kernel
private theorem disp_134 : dispCheck 134 = true := by decide +kernel
private theorem disp_135 : dispCheck 135 = true := by decide +kernel
private theorem disp_136 : dispCheck 136 = true := by decide +kernel
private theorem disp_137 : dispCheck 137 = true := by decide +kernel
private theorem disp_138 : dispCheck 138 = true := by decide +kernel
private theorem disp_139 : dispCheck 139 = true := by decide +kernel
private theorem disp_140 : dispCheck 140 = true := by decide +kernel
private theorem disp_141 : dispCheck 141 = true := by decide +kernel
private theorem disp_142 : dispCheck 142 = true := by decide +kernel
private theorem disp_143 : dispCheck 143 = true := by decide +kernel
private theorem disp_144 : dispCheck 144 = true := by decide +kernel
private theorem disp_145 : dispCheck 145 = true := by decide +kernel
private theorem disp_146 : dispCheck 146 = true := by decide +kernel
private theorem disp_147 : dispCheck 147 = true := by decide +kernel
private theorem disp_148 : dispCheck 148 = true := by decide +kernel
private theorem disp_149 : dispCheck 149 = true := by decide +kernel
private theorem disp_150 : dispCheck 150 = true := by decide +kernel
private theorem disp_151 : dispCheck 151 = true := by decide +kernel
private theorem disp_152 : dispCheck 152 = true := by decide +kernel
private theorem disp_153 : dispCheck 153 = true := by decide +kernel
private theorem disp_154 : dispCheck 154 = true := by decide +kernel
private theorem disp_155 : dispCheck 155 = true := by decide +kernel
private theorem disp_156 : dispCheck 156 = true := by decide +kernel
private theorem disp_157 : dispCheck 157 = true := by decide +kernel
private theorem disp_158 : dispCheck 158 = true := by decide +kernel
private theorem disp_159 : dispCheck 159 = true := by decide +kernel
private theorem disp_160 : dispCheck 160 = true := by decide +kernel
private theorem disp_161 : dispCheck 161 = true := by decide +kernel
private theorem disp_162 : dispCheck 162 = true := by decide +kernel
private theorem disp_163 : dispCheck 163 = true := by decide +kernel
private theorem disp_164 : dispCheck 164 = true := by decide +kernel
private theorem disp_165 : dispCheck 165 = true := by decide +kernel
private theorem disp_166 : dispCheck 166 = true := by decide +kernel
private theorem disp_167 : dispCheck 167 = true := by decide +kernel
private theorem disp_168 : dispCheck 168 = true := by decide +kernel
private theorem disp_169 : dispCheck 169 = true := by decide +kernel
private theorem disp_170 : dispCheck 170 = true := by decide +kernel
private theorem disp_171 : dispCheck 171 = true := by decide +kernel
private theorem disp_172 : dispCheck 172 = true := by decide +kernel
private theorem disp_173 : dispCheck 173 = true := by decide +kernel
private theorem disp_174 : dispCheck 174 = true := by decide +kernel
private theorem disp_175 : dispCheck 175 = true := by decide +kernel
private theorem disp_176 : dispCheck 176 = true := by decide +kernel
private theorem disp_177 : dispCheck 177 = true := by decide +kernel
private theorem disp_178 : dispCheck 178 = true := by decide +kernel
private theorem disp_179 : dispCheck 179 = true := by decide +kernel
private theorem disp_180 : dispCheck 180 = true := by decide +kernel
private theorem disp_181 : dispCheck 181 = true := by decide +kernel
private theorem disp_182 : dispCheck 182 = true := by decide +kernel
private theorem disp_183 : dispCheck 183 = true := by decide +kernel
private theorem disp_184 : dispCheck 184 = true := by decide +kernel
private theorem disp_185 : dispCheck 185 = true := by decide +kernel
private theorem disp_186 : dispCheck 186 = true := by decide +kernel
private theorem disp_187 : dispCheck 187 = true := by decide +kernel
private theorem disp_188 : dispCheck 188 = true := by decide +kernel
private theorem disp_189 : dispCheck 189 = true := by decide +kernel
private theorem disp_190 : dispCheck 190 = true := by decide +kernel
private theorem disp_191 : dispCheck 191 = true := by decide +kernel
private theorem disp_192 : dispCheck 192 = true := by decide +kernel
private theorem disp_193 : dispCheck 193 = true := by decide +kernel
private theorem disp_194 : dispCheck 194 = true := by decide +kernel
private theorem disp_195 : dispCheck 195 = true := by decide +kernel
private theorem disp_196 : dispCheck 196 = true := by decide +kernel
private theorem disp_197 : dispCheck 197 = true := by decide +kernel
private theorem disp_198 : dispCheck 198 = true := by decide +kernel
private theorem disp_199 : dispCheck 199 = true := by decide +kernel
private theorem disp_200 : dispCheck 200 = true := by decide +kernel
private theorem disp_201 : dispCheck 201 = true := by decide +kernel
private theorem disp_202 : dispCheck 202 = true := by decide +kernel
private theorem disp_203 : dispCheck 203 = true := by decide +kernel
private theorem disp_204 : dispCheck 204 = true := by decide +kernel
private theorem disp_205 : dispCheck 205 = true := by decide +kernel
private theorem disp_206 : dispCheck 206 = true := by decide +kernel
private theorem disp_207 : dispCheck 207 = true := by decide +kernel
private theorem disp_208 : dispCheck 208 = true := by decide +kernel
private theorem disp_209 : dispCheck 209 = true := by decide +kernel
theorem dispCheck_all : (List.range 210).all dispCheck = true := by
  have h : (List.range 210) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, true_and, and_true, disp_0, disp_1, disp_2, disp_3, disp_4, disp_5, disp_6, disp_7, disp_8, disp_9, disp_10, disp_11, disp_12, disp_13, disp_14, disp_15, disp_16, disp_17, disp_18, disp_19, disp_20, disp_21, disp_22, disp_23, disp_24, disp_25, disp_26, disp_27, disp_28, disp_29, disp_30, disp_31, disp_32, disp_33, disp_34, disp_35, disp_36, disp_37, disp_38, disp_39, disp_40, disp_41, disp_42, disp_43, disp_44, disp_45, disp_46, disp_47, disp_48, disp_49, disp_50, disp_51, disp_52, disp_53, disp_54, disp_55, disp_56, disp_57, disp_58, disp_59, disp_60, disp_61, disp_62, disp_63, disp_64, disp_65, disp_66, disp_67, disp_68, disp_69, disp_70, disp_71, disp_72, disp_73, disp_74, disp_75, disp_76, disp_77, disp_78, disp_79, disp_80, disp_81, disp_82, disp_83, disp_84, disp_85, disp_86, disp_87, disp_88, disp_89, disp_90, disp_91, disp_92, disp_93, disp_94, disp_95, disp_96, disp_97, disp_98, disp_99, disp_100, disp_101, disp_102, disp_103, disp_104, disp_105, disp_106, disp_107, disp_108, disp_109, disp_110, disp_111, disp_112, disp_113, disp_114, disp_115, disp_116, disp_117, disp_118, disp_119, disp_120, disp_121, disp_122, disp_123, disp_124, disp_125, disp_126, disp_127, disp_128, disp_129, disp_130, disp_131, disp_132, disp_133, disp_134, disp_135, disp_136, disp_137, disp_138, disp_139, disp_140, disp_141, disp_142, disp_143, disp_144, disp_145, disp_146, disp_147, disp_148, disp_149, disp_150, disp_151, disp_152, disp_153, disp_154, disp_155, disp_156, disp_157, disp_158, disp_159, disp_160, disp_161, disp_162, disp_163, disp_164, disp_165, disp_166, disp_167, disp_168, disp_169, disp_170, disp_171, disp_172, disp_173, disp_174, disp_175, disp_176, disp_177, disp_178, disp_179, disp_180, disp_181, disp_182, disp_183, disp_184, disp_185, disp_186, disp_187, disp_188, disp_189, disp_190, disp_191, disp_192, disp_193, disp_194, disp_195, disp_196, disp_197, disp_198, disp_199, disp_200, disp_201, disp_202, disp_203, disp_204, disp_205, disp_206, disp_207, disp_208, disp_209]

private theorem tail_0 : tailCheck 0 = true := by decide +kernel
private theorem tail_1 : tailCheck 1 = true := by decide +kernel
private theorem tail_2 : tailCheck 2 = true := by decide +kernel
private theorem tail_3 : tailCheck 3 = true := by decide +kernel
private theorem tail_4 : tailCheck 4 = true := by decide +kernel
private theorem tail_5 : tailCheck 5 = true := by decide +kernel
private theorem tail_6 : tailCheck 6 = true := by decide +kernel
private theorem tail_7 : tailCheck 7 = true := by decide +kernel
private theorem tail_8 : tailCheck 8 = true := by decide +kernel
private theorem tail_9 : tailCheck 9 = true := by decide +kernel
private theorem tail_10 : tailCheck 10 = true := by decide +kernel
private theorem tail_11 : tailCheck 11 = true := by decide +kernel
private theorem tail_12 : tailCheck 12 = true := by decide +kernel
private theorem tail_13 : tailCheck 13 = true := by decide +kernel
private theorem tail_14 : tailCheck 14 = true := by decide +kernel
private theorem tail_15 : tailCheck 15 = true := by decide +kernel
private theorem tail_16 : tailCheck 16 = true := by decide +kernel
private theorem tail_17 : tailCheck 17 = true := by decide +kernel
private theorem tail_18 : tailCheck 18 = true := by decide +kernel
private theorem tail_19 : tailCheck 19 = true := by decide +kernel
private theorem tail_20 : tailCheck 20 = true := by decide +kernel
private theorem tail_21 : tailCheck 21 = true := by decide +kernel
private theorem tail_22 : tailCheck 22 = true := by decide +kernel
private theorem tail_23 : tailCheck 23 = true := by decide +kernel
private theorem tail_24 : tailCheck 24 = true := by decide +kernel
private theorem tail_25 : tailCheck 25 = true := by decide +kernel
private theorem tail_26 : tailCheck 26 = true := by decide +kernel
private theorem tail_27 : tailCheck 27 = true := by decide +kernel
private theorem tail_28 : tailCheck 28 = true := by decide +kernel
private theorem tail_29 : tailCheck 29 = true := by decide +kernel
private theorem tail_30 : tailCheck 30 = true := by decide +kernel
private theorem tail_31 : tailCheck 31 = true := by decide +kernel
private theorem tail_32 : tailCheck 32 = true := by decide +kernel
private theorem tail_33 : tailCheck 33 = true := by decide +kernel
private theorem tail_34 : tailCheck 34 = true := by decide +kernel
private theorem tail_35 : tailCheck 35 = true := by decide +kernel
private theorem tail_36 : tailCheck 36 = true := by decide +kernel
private theorem tail_37 : tailCheck 37 = true := by decide +kernel
private theorem tail_38 : tailCheck 38 = true := by decide +kernel
private theorem tail_39 : tailCheck 39 = true := by decide +kernel
private theorem tail_40 : tailCheck 40 = true := by decide +kernel
private theorem tail_41 : tailCheck 41 = true := by decide +kernel
private theorem tail_42 : tailCheck 42 = true := by decide +kernel
private theorem tail_43 : tailCheck 43 = true := by decide +kernel
private theorem tail_44 : tailCheck 44 = true := by decide +kernel
private theorem tail_45 : tailCheck 45 = true := by decide +kernel
private theorem tail_46 : tailCheck 46 = true := by decide +kernel
private theorem tail_47 : tailCheck 47 = true := by decide +kernel
private theorem tail_48 : tailCheck 48 = true := by decide +kernel
private theorem tail_49 : tailCheck 49 = true := by decide +kernel
private theorem tail_50 : tailCheck 50 = true := by decide +kernel
private theorem tail_51 : tailCheck 51 = true := by decide +kernel
private theorem tail_52 : tailCheck 52 = true := by decide +kernel
private theorem tail_53 : tailCheck 53 = true := by decide +kernel
private theorem tail_54 : tailCheck 54 = true := by decide +kernel
private theorem tail_55 : tailCheck 55 = true := by decide +kernel
private theorem tail_56 : tailCheck 56 = true := by decide +kernel
private theorem tail_57 : tailCheck 57 = true := by decide +kernel
private theorem tail_58 : tailCheck 58 = true := by decide +kernel
private theorem tail_59 : tailCheck 59 = true := by decide +kernel
private theorem tail_60 : tailCheck 60 = true := by decide +kernel
private theorem tail_61 : tailCheck 61 = true := by decide +kernel
private theorem tail_62 : tailCheck 62 = true := by decide +kernel
private theorem tail_63 : tailCheck 63 = true := by decide +kernel
private theorem tail_64 : tailCheck 64 = true := by decide +kernel
private theorem tail_65 : tailCheck 65 = true := by decide +kernel
private theorem tail_66 : tailCheck 66 = true := by decide +kernel
private theorem tail_67 : tailCheck 67 = true := by decide +kernel
private theorem tail_68 : tailCheck 68 = true := by decide +kernel
private theorem tail_69 : tailCheck 69 = true := by decide +kernel
private theorem tail_70 : tailCheck 70 = true := by decide +kernel
private theorem tail_71 : tailCheck 71 = true := by decide +kernel
private theorem tail_72 : tailCheck 72 = true := by decide +kernel
private theorem tail_73 : tailCheck 73 = true := by decide +kernel
private theorem tail_74 : tailCheck 74 = true := by decide +kernel
private theorem tail_75 : tailCheck 75 = true := by decide +kernel
private theorem tail_76 : tailCheck 76 = true := by decide +kernel
private theorem tail_77 : tailCheck 77 = true := by decide +kernel
private theorem tail_78 : tailCheck 78 = true := by decide +kernel
private theorem tail_79 : tailCheck 79 = true := by decide +kernel
private theorem tail_80 : tailCheck 80 = true := by decide +kernel
private theorem tail_81 : tailCheck 81 = true := by decide +kernel
private theorem tail_82 : tailCheck 82 = true := by decide +kernel
private theorem tail_83 : tailCheck 83 = true := by decide +kernel
private theorem tail_84 : tailCheck 84 = true := by decide +kernel
private theorem tail_85 : tailCheck 85 = true := by decide +kernel
private theorem tail_86 : tailCheck 86 = true := by decide +kernel
private theorem tail_87 : tailCheck 87 = true := by decide +kernel
private theorem tail_88 : tailCheck 88 = true := by decide +kernel
private theorem tail_89 : tailCheck 89 = true := by decide +kernel
private theorem tail_90 : tailCheck 90 = true := by decide +kernel
private theorem tail_91 : tailCheck 91 = true := by decide +kernel
private theorem tail_92 : tailCheck 92 = true := by decide +kernel
private theorem tail_93 : tailCheck 93 = true := by decide +kernel
private theorem tail_94 : tailCheck 94 = true := by decide +kernel
private theorem tail_95 : tailCheck 95 = true := by decide +kernel
private theorem tail_96 : tailCheck 96 = true := by decide +kernel
private theorem tail_97 : tailCheck 97 = true := by decide +kernel
private theorem tail_98 : tailCheck 98 = true := by decide +kernel
private theorem tail_99 : tailCheck 99 = true := by decide +kernel
private theorem tail_100 : tailCheck 100 = true := by decide +kernel
private theorem tail_101 : tailCheck 101 = true := by decide +kernel
private theorem tail_102 : tailCheck 102 = true := by decide +kernel
private theorem tail_103 : tailCheck 103 = true := by decide +kernel
private theorem tail_104 : tailCheck 104 = true := by decide +kernel
private theorem tail_105 : tailCheck 105 = true := by decide +kernel
private theorem tail_106 : tailCheck 106 = true := by decide +kernel
private theorem tail_107 : tailCheck 107 = true := by decide +kernel
private theorem tail_108 : tailCheck 108 = true := by decide +kernel
private theorem tail_109 : tailCheck 109 = true := by decide +kernel
private theorem tail_110 : tailCheck 110 = true := by decide +kernel
private theorem tail_111 : tailCheck 111 = true := by decide +kernel
private theorem tail_112 : tailCheck 112 = true := by decide +kernel
private theorem tail_113 : tailCheck 113 = true := by decide +kernel
private theorem tail_114 : tailCheck 114 = true := by decide +kernel
private theorem tail_115 : tailCheck 115 = true := by decide +kernel
private theorem tail_116 : tailCheck 116 = true := by decide +kernel
private theorem tail_117 : tailCheck 117 = true := by decide +kernel
private theorem tail_118 : tailCheck 118 = true := by decide +kernel
private theorem tail_119 : tailCheck 119 = true := by decide +kernel
private theorem tail_120 : tailCheck 120 = true := by decide +kernel
private theorem tail_121 : tailCheck 121 = true := by decide +kernel
private theorem tail_122 : tailCheck 122 = true := by decide +kernel
private theorem tail_123 : tailCheck 123 = true := by decide +kernel
private theorem tail_124 : tailCheck 124 = true := by decide +kernel
private theorem tail_125 : tailCheck 125 = true := by decide +kernel
private theorem tail_126 : tailCheck 126 = true := by decide +kernel
private theorem tail_127 : tailCheck 127 = true := by decide +kernel
private theorem tail_128 : tailCheck 128 = true := by decide +kernel
private theorem tail_129 : tailCheck 129 = true := by decide +kernel
private theorem tail_130 : tailCheck 130 = true := by decide +kernel
private theorem tail_131 : tailCheck 131 = true := by decide +kernel
private theorem tail_132 : tailCheck 132 = true := by decide +kernel
private theorem tail_133 : tailCheck 133 = true := by decide +kernel
private theorem tail_134 : tailCheck 134 = true := by decide +kernel
private theorem tail_135 : tailCheck 135 = true := by decide +kernel
private theorem tail_136 : tailCheck 136 = true := by decide +kernel
private theorem tail_137 : tailCheck 137 = true := by decide +kernel
private theorem tail_138 : tailCheck 138 = true := by decide +kernel
private theorem tail_139 : tailCheck 139 = true := by decide +kernel
private theorem tail_140 : tailCheck 140 = true := by decide +kernel
private theorem tail_141 : tailCheck 141 = true := by decide +kernel
private theorem tail_142 : tailCheck 142 = true := by decide +kernel
private theorem tail_143 : tailCheck 143 = true := by decide +kernel
private theorem tail_144 : tailCheck 144 = true := by decide +kernel
private theorem tail_145 : tailCheck 145 = true := by decide +kernel
private theorem tail_146 : tailCheck 146 = true := by decide +kernel
private theorem tail_147 : tailCheck 147 = true := by decide +kernel
private theorem tail_148 : tailCheck 148 = true := by decide +kernel
private theorem tail_149 : tailCheck 149 = true := by decide +kernel
private theorem tail_150 : tailCheck 150 = true := by decide +kernel
private theorem tail_151 : tailCheck 151 = true := by decide +kernel
private theorem tail_152 : tailCheck 152 = true := by decide +kernel
private theorem tail_153 : tailCheck 153 = true := by decide +kernel
private theorem tail_154 : tailCheck 154 = true := by decide +kernel
private theorem tail_155 : tailCheck 155 = true := by decide +kernel
private theorem tail_156 : tailCheck 156 = true := by decide +kernel
private theorem tail_157 : tailCheck 157 = true := by decide +kernel
private theorem tail_158 : tailCheck 158 = true := by decide +kernel
private theorem tail_159 : tailCheck 159 = true := by decide +kernel
private theorem tail_160 : tailCheck 160 = true := by decide +kernel
private theorem tail_161 : tailCheck 161 = true := by decide +kernel
private theorem tail_162 : tailCheck 162 = true := by decide +kernel
private theorem tail_163 : tailCheck 163 = true := by decide +kernel
private theorem tail_164 : tailCheck 164 = true := by decide +kernel
private theorem tail_165 : tailCheck 165 = true := by decide +kernel
private theorem tail_166 : tailCheck 166 = true := by decide +kernel
private theorem tail_167 : tailCheck 167 = true := by decide +kernel
private theorem tail_168 : tailCheck 168 = true := by decide +kernel
private theorem tail_169 : tailCheck 169 = true := by decide +kernel
private theorem tail_170 : tailCheck 170 = true := by decide +kernel
private theorem tail_171 : tailCheck 171 = true := by decide +kernel
private theorem tail_172 : tailCheck 172 = true := by decide +kernel
private theorem tail_173 : tailCheck 173 = true := by decide +kernel
private theorem tail_174 : tailCheck 174 = true := by decide +kernel
private theorem tail_175 : tailCheck 175 = true := by decide +kernel
private theorem tail_176 : tailCheck 176 = true := by decide +kernel
private theorem tail_177 : tailCheck 177 = true := by decide +kernel
private theorem tail_178 : tailCheck 178 = true := by decide +kernel
private theorem tail_179 : tailCheck 179 = true := by decide +kernel
private theorem tail_180 : tailCheck 180 = true := by decide +kernel
private theorem tail_181 : tailCheck 181 = true := by decide +kernel
private theorem tail_182 : tailCheck 182 = true := by decide +kernel
private theorem tail_183 : tailCheck 183 = true := by decide +kernel
private theorem tail_184 : tailCheck 184 = true := by decide +kernel
private theorem tail_185 : tailCheck 185 = true := by decide +kernel
private theorem tail_186 : tailCheck 186 = true := by decide +kernel
private theorem tail_187 : tailCheck 187 = true := by decide +kernel
private theorem tail_188 : tailCheck 188 = true := by decide +kernel
private theorem tail_189 : tailCheck 189 = true := by decide +kernel
private theorem tail_190 : tailCheck 190 = true := by decide +kernel
private theorem tail_191 : tailCheck 191 = true := by decide +kernel
private theorem tail_192 : tailCheck 192 = true := by decide +kernel
private theorem tail_193 : tailCheck 193 = true := by decide +kernel
private theorem tail_194 : tailCheck 194 = true := by decide +kernel
theorem tailCheck_all : (List.range 195).all tailCheck = true := by
  have h : (List.range 195) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, true_and, and_true, tail_0, tail_1, tail_2, tail_3, tail_4, tail_5, tail_6, tail_7, tail_8, tail_9, tail_10, tail_11, tail_12, tail_13, tail_14, tail_15, tail_16, tail_17, tail_18, tail_19, tail_20, tail_21, tail_22, tail_23, tail_24, tail_25, tail_26, tail_27, tail_28, tail_29, tail_30, tail_31, tail_32, tail_33, tail_34, tail_35, tail_36, tail_37, tail_38, tail_39, tail_40, tail_41, tail_42, tail_43, tail_44, tail_45, tail_46, tail_47, tail_48, tail_49, tail_50, tail_51, tail_52, tail_53, tail_54, tail_55, tail_56, tail_57, tail_58, tail_59, tail_60, tail_61, tail_62, tail_63, tail_64, tail_65, tail_66, tail_67, tail_68, tail_69, tail_70, tail_71, tail_72, tail_73, tail_74, tail_75, tail_76, tail_77, tail_78, tail_79, tail_80, tail_81, tail_82, tail_83, tail_84, tail_85, tail_86, tail_87, tail_88, tail_89, tail_90, tail_91, tail_92, tail_93, tail_94, tail_95, tail_96, tail_97, tail_98, tail_99, tail_100, tail_101, tail_102, tail_103, tail_104, tail_105, tail_106, tail_107, tail_108, tail_109, tail_110, tail_111, tail_112, tail_113, tail_114, tail_115, tail_116, tail_117, tail_118, tail_119, tail_120, tail_121, tail_122, tail_123, tail_124, tail_125, tail_126, tail_127, tail_128, tail_129, tail_130, tail_131, tail_132, tail_133, tail_134, tail_135, tail_136, tail_137, tail_138, tail_139, tail_140, tail_141, tail_142, tail_143, tail_144, tail_145, tail_146, tail_147, tail_148, tail_149, tail_150, tail_151, tail_152, tail_153, tail_154, tail_155, tail_156, tail_157, tail_158, tail_159, tail_160, tail_161, tail_162, tail_163, tail_164, tail_165, tail_166, tail_167, tail_168, tail_169, tail_170, tail_171, tail_172, tail_173, tail_174, tail_175, tail_176, tail_177, tail_178, tail_179, tail_180, tail_181, tail_182, tail_183, tail_184, tail_185, tail_186, tail_187, tail_188, tail_189, tail_190, tail_191, tail_192, tail_193, tail_194]
private theorem nojoin_0_3_0 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 0) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 0 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_1 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 1) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 1 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_2 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 2) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 2 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_3 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 3) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 3 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_4 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 4) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 4 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_5 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 5) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 5 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_6 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 6) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 6 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_3_7 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 3 i 7) (posDirs t (14-3+i) t'))
          (prefixPosSpec 0 t 3 i 7 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_0 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 0) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 0 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_1 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 1) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 1 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_2 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 2) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 2 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_3 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 3) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 3 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_4 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 4) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 4 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_5 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 5) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 5 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_6 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 6) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 6 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_4_7 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 4 i 7) (posDirs t (14-4+i) t'))
          (prefixPosSpec 0 t 4 i 7 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_0 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 0) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 0 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_1 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 1) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 1 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_2 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 2) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 2 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_3 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 3) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 3 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_4 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 4) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 4 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_5 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 5) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 5 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_6 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 6) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 6 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_5_7 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 5 i 7) (posDirs t (14-5+i) t'))
          (prefixPosSpec 0 t 5 i 7 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_0 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 0) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 0 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_1 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 1) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 1 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_2 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 2) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 2 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_3 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 3) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 3 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_4 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 4) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 4 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_5 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 5) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 5 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_6 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 6) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 6 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_6_7 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 6 i 7) (posDirs t (14-6+i) t'))
          (prefixPosSpec 0 t 6 i 7 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_0 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 0) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 0 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_1 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 1) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 1 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_2 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 2) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 2 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_3 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 3) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 3 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_4 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 4) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 4 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_5 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 5) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 5 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_6 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 6) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 6 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_7_7 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 7 i 7) (posDirs t (14-7+i) t'))
          (prefixPosSpec 0 t 7 i 7 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_0 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 0) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 0 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_1 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 1) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 1 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_2 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 2) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 2 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_3 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 3) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 3 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_4 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 4) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 4 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_5 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 5) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 5 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_6 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 6) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 6 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_8_7 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 8 i 7) (posDirs t (14-8+i) t'))
          (prefixPosSpec 0 t 8 i 7 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_0 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 0) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 0 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_1 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 1) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 1 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_2 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 2) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 2 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_3 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 3) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 3 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_4 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 4) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 4 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_5 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 5) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 5 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_6 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 6) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 6 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_9_7 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 9 i 7) (posDirs t (14-9+i) t'))
          (prefixPosSpec 0 t 9 i 7 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_0 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 0) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 0 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_1 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 1) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 1 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_2 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 2) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 2 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_3 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 3) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 3 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_4 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 4) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 4 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_5 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 5) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 5 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_6 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 6) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 6 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_10_7 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 10 i 7) (posDirs t (14-10+i) t'))
          (prefixPosSpec 0 t 10 i 7 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_0 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 0) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 0 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_1 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 1) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 1 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_2 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 2) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 2 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_3 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 3) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 3 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_4 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 4) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 4 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_5 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 5) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 5 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_6 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 6) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 6 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_11_7 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 11 i 7) (posDirs t (14-11+i) t'))
          (prefixPosSpec 0 t 11 i 7 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_0 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 0) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 0 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_1 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 1) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 1 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_2 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 2) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 2 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_3 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 3) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 3 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_4 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 4) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 4 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_5 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 5) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 5 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_6 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 6) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 6 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_12_7 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 12 i 7) (posDirs t (14-12+i) t'))
          (prefixPosSpec 0 t 12 i 7 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_0 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 0) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 0 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_1 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 1) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 1 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_2 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 2) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 2 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_3 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 3) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 3 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_4 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 4) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 4 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_5 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 5) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 5 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_6 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 6) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 6 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_13_7 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 13 i 7) (posDirs t (14-13+i) t'))
          (prefixPosSpec 0 t 13 i 7 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_0 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 0) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 0 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_1 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 1) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 1 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_2 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 2) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 2 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_3 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 3) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 3 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_4 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 4) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 4 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_5 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 5) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 5 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_6 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 6) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 6 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_0_14_7 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 0 t 14 i 7) (posDirs t (14-14+i) t'))
          (prefixPosSpec 0 t 14 i 7 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
theorem nojoinCheck_0 : nojoinCheck 0 = true := by
  unfold nojoinCheck
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro bits hb
  have hb := List.mem_range.mp hb
  obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp ha
  interval_cases j <;> interval_cases bits
  · exact nojoin_0_3_0
  · exact nojoin_0_3_1
  · exact nojoin_0_3_2
  · exact nojoin_0_3_3
  · exact nojoin_0_3_4
  · exact nojoin_0_3_5
  · exact nojoin_0_3_6
  · exact nojoin_0_3_7
  · exact nojoin_0_4_0
  · exact nojoin_0_4_1
  · exact nojoin_0_4_2
  · exact nojoin_0_4_3
  · exact nojoin_0_4_4
  · exact nojoin_0_4_5
  · exact nojoin_0_4_6
  · exact nojoin_0_4_7
  · exact nojoin_0_5_0
  · exact nojoin_0_5_1
  · exact nojoin_0_5_2
  · exact nojoin_0_5_3
  · exact nojoin_0_5_4
  · exact nojoin_0_5_5
  · exact nojoin_0_5_6
  · exact nojoin_0_5_7
  · exact nojoin_0_6_0
  · exact nojoin_0_6_1
  · exact nojoin_0_6_2
  · exact nojoin_0_6_3
  · exact nojoin_0_6_4
  · exact nojoin_0_6_5
  · exact nojoin_0_6_6
  · exact nojoin_0_6_7
  · exact nojoin_0_7_0
  · exact nojoin_0_7_1
  · exact nojoin_0_7_2
  · exact nojoin_0_7_3
  · exact nojoin_0_7_4
  · exact nojoin_0_7_5
  · exact nojoin_0_7_6
  · exact nojoin_0_7_7
  · exact nojoin_0_8_0
  · exact nojoin_0_8_1
  · exact nojoin_0_8_2
  · exact nojoin_0_8_3
  · exact nojoin_0_8_4
  · exact nojoin_0_8_5
  · exact nojoin_0_8_6
  · exact nojoin_0_8_7
  · exact nojoin_0_9_0
  · exact nojoin_0_9_1
  · exact nojoin_0_9_2
  · exact nojoin_0_9_3
  · exact nojoin_0_9_4
  · exact nojoin_0_9_5
  · exact nojoin_0_9_6
  · exact nojoin_0_9_7
  · exact nojoin_0_10_0
  · exact nojoin_0_10_1
  · exact nojoin_0_10_2
  · exact nojoin_0_10_3
  · exact nojoin_0_10_4
  · exact nojoin_0_10_5
  · exact nojoin_0_10_6
  · exact nojoin_0_10_7
  · exact nojoin_0_11_0
  · exact nojoin_0_11_1
  · exact nojoin_0_11_2
  · exact nojoin_0_11_3
  · exact nojoin_0_11_4
  · exact nojoin_0_11_5
  · exact nojoin_0_11_6
  · exact nojoin_0_11_7
  · exact nojoin_0_12_0
  · exact nojoin_0_12_1
  · exact nojoin_0_12_2
  · exact nojoin_0_12_3
  · exact nojoin_0_12_4
  · exact nojoin_0_12_5
  · exact nojoin_0_12_6
  · exact nojoin_0_12_7
  · exact nojoin_0_13_0
  · exact nojoin_0_13_1
  · exact nojoin_0_13_2
  · exact nojoin_0_13_3
  · exact nojoin_0_13_4
  · exact nojoin_0_13_5
  · exact nojoin_0_13_6
  · exact nojoin_0_13_7
  · exact nojoin_0_14_0
  · exact nojoin_0_14_1
  · exact nojoin_0_14_2
  · exact nojoin_0_14_3
  · exact nojoin_0_14_4
  · exact nojoin_0_14_5
  · exact nojoin_0_14_6
  · exact nojoin_0_14_7

private theorem nojoin_1_3_0 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 0) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 0 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_1 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 1) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 1 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_2 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 2) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 2 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_3 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 3) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 3 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_4 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 4) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 4 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_5 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 5) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 5 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_6 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 6) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 6 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_3_7 : ((List.range 3).all fun i => i < prefixN 3 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=3 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 3 i 7) (posDirs t (14-3+i) t'))
          (prefixPosSpec 1 t 3 i 7 t') (posObl (14-3+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_0 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 0) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 0 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_1 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 1) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 1 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_2 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 2) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 2 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_3 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 3) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 3 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_4 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 4) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 4 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_5 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 5) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 5 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_6 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 6) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 6 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_4_7 : ((List.range 4).all fun i => i < prefixN 4 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=4 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 4 i 7) (posDirs t (14-4+i) t'))
          (prefixPosSpec 1 t 4 i 7 t') (posObl (14-4+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_0 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 0) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 0 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_1 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 1) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 1 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_2 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 2) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 2 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_3 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 3) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 3 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_4 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 4) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 4 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_5 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 5) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 5 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_6 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 6) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 6 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_5_7 : ((List.range 5).all fun i => i < prefixN 5 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=5 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 5 i 7) (posDirs t (14-5+i) t'))
          (prefixPosSpec 1 t 5 i 7 t') (posObl (14-5+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_0 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 0) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 0 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_1 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 1) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 1 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_2 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 2) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 2 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_3 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 3) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 3 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_4 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 4) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 4 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_5 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 5) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 5 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_6 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 6) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 6 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_6_7 : ((List.range 6).all fun i => i < prefixN 6 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=6 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 6 i 7) (posDirs t (14-6+i) t'))
          (prefixPosSpec 1 t 6 i 7 t') (posObl (14-6+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_0 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 0) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 0 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_1 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 1) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 1 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_2 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 2) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 2 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_3 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 3) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 3 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_4 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 4) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 4 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_5 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 5) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 5 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_6 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 6) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 6 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_7_7 : ((List.range 7).all fun i => i < prefixN 7 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=7 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 7 i 7) (posDirs t (14-7+i) t'))
          (prefixPosSpec 1 t 7 i 7 t') (posObl (14-7+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_0 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 0) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 0 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_1 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 1) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 1 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_2 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 2) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 2 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_3 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 3) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 3 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_4 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 4) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 4 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_5 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 5) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 5 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_6 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 6) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 6 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_8_7 : ((List.range 8).all fun i => i < prefixN 8 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=8 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 8 i 7) (posDirs t (14-8+i) t'))
          (prefixPosSpec 1 t 8 i 7 t') (posObl (14-8+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_0 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 0) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 0 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_1 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 1) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 1 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_2 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 2) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 2 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_3 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 3) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 3 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_4 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 4) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 4 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_5 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 5) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 5 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_6 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 6) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 6 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_9_7 : ((List.range 9).all fun i => i < prefixN 9 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=9 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 9 i 7) (posDirs t (14-9+i) t'))
          (prefixPosSpec 1 t 9 i 7 t') (posObl (14-9+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_0 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 0) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 0 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_1 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 1) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 1 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_2 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 2) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 2 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_3 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 3) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 3 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_4 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 4) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 4 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_5 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 5) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 5 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_6 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 6) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 6 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_10_7 : ((List.range 10).all fun i => i < prefixN 10 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=10 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 10 i 7) (posDirs t (14-10+i) t'))
          (prefixPosSpec 1 t 10 i 7 t') (posObl (14-10+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_0 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 0) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 0 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_1 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 1) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 1 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_2 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 2) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 2 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_3 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 3) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 3 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_4 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 4) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 4 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_5 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 5) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 5 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_6 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 6) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 6 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_11_7 : ((List.range 11).all fun i => i < prefixN 11 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=11 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 11 i 7) (posDirs t (14-11+i) t'))
          (prefixPosSpec 1 t 11 i 7 t') (posObl (14-11+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_0 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 0) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 0 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_1 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 1) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 1 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_2 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 2) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 2 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_3 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 3) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 3 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_4 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 4) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 4 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_5 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 5) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 5 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_6 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 6) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 6 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_12_7 : ((List.range 12).all fun i => i < prefixN 12 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=12 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 12 i 7) (posDirs t (14-12+i) t'))
          (prefixPosSpec 1 t 12 i 7 t') (posObl (14-12+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_0 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 0) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 0 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_1 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 1) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 1 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_2 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 2) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 2 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_3 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 3) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 3 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_4 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 4) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 4 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_5 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 5) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 5 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_6 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 6) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 6 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_13_7 : ((List.range 13).all fun i => i < prefixN 13 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=13 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 13 i 7) (posDirs t (14-13+i) t'))
          (prefixPosSpec 1 t 13 i 7 t') (posObl (14-13+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_0 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 0) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 0 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_1 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 1) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 1 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_2 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 2) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 2 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_3 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 3) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 3 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_4 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 4) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 4 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_5 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 5) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 5 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_6 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 6) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 6 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
private theorem nojoin_1_14_7 : ((List.range 14).all fun i => i < prefixN 14 ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=14 && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc 1 t 14 i 7) (posDirs t (14-14+i) t'))
          (prefixPosSpec 1 t 14 i 7 t') (posObl (14-14+i)) posKnown posKeep) = true := by decide +kernel
theorem nojoinCheck_1 : nojoinCheck 1 = true := by
  unfold nojoinCheck
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro bits hb
  have hb := List.mem_range.mp hb
  obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp ha
  interval_cases j <;> interval_cases bits
  · exact nojoin_1_3_0
  · exact nojoin_1_3_1
  · exact nojoin_1_3_2
  · exact nojoin_1_3_3
  · exact nojoin_1_3_4
  · exact nojoin_1_3_5
  · exact nojoin_1_3_6
  · exact nojoin_1_3_7
  · exact nojoin_1_4_0
  · exact nojoin_1_4_1
  · exact nojoin_1_4_2
  · exact nojoin_1_4_3
  · exact nojoin_1_4_4
  · exact nojoin_1_4_5
  · exact nojoin_1_4_6
  · exact nojoin_1_4_7
  · exact nojoin_1_5_0
  · exact nojoin_1_5_1
  · exact nojoin_1_5_2
  · exact nojoin_1_5_3
  · exact nojoin_1_5_4
  · exact nojoin_1_5_5
  · exact nojoin_1_5_6
  · exact nojoin_1_5_7
  · exact nojoin_1_6_0
  · exact nojoin_1_6_1
  · exact nojoin_1_6_2
  · exact nojoin_1_6_3
  · exact nojoin_1_6_4
  · exact nojoin_1_6_5
  · exact nojoin_1_6_6
  · exact nojoin_1_6_7
  · exact nojoin_1_7_0
  · exact nojoin_1_7_1
  · exact nojoin_1_7_2
  · exact nojoin_1_7_3
  · exact nojoin_1_7_4
  · exact nojoin_1_7_5
  · exact nojoin_1_7_6
  · exact nojoin_1_7_7
  · exact nojoin_1_8_0
  · exact nojoin_1_8_1
  · exact nojoin_1_8_2
  · exact nojoin_1_8_3
  · exact nojoin_1_8_4
  · exact nojoin_1_8_5
  · exact nojoin_1_8_6
  · exact nojoin_1_8_7
  · exact nojoin_1_9_0
  · exact nojoin_1_9_1
  · exact nojoin_1_9_2
  · exact nojoin_1_9_3
  · exact nojoin_1_9_4
  · exact nojoin_1_9_5
  · exact nojoin_1_9_6
  · exact nojoin_1_9_7
  · exact nojoin_1_10_0
  · exact nojoin_1_10_1
  · exact nojoin_1_10_2
  · exact nojoin_1_10_3
  · exact nojoin_1_10_4
  · exact nojoin_1_10_5
  · exact nojoin_1_10_6
  · exact nojoin_1_10_7
  · exact nojoin_1_11_0
  · exact nojoin_1_11_1
  · exact nojoin_1_11_2
  · exact nojoin_1_11_3
  · exact nojoin_1_11_4
  · exact nojoin_1_11_5
  · exact nojoin_1_11_6
  · exact nojoin_1_11_7
  · exact nojoin_1_12_0
  · exact nojoin_1_12_1
  · exact nojoin_1_12_2
  · exact nojoin_1_12_3
  · exact nojoin_1_12_4
  · exact nojoin_1_12_5
  · exact nojoin_1_12_6
  · exact nojoin_1_12_7
  · exact nojoin_1_13_0
  · exact nojoin_1_13_1
  · exact nojoin_1_13_2
  · exact nojoin_1_13_3
  · exact nojoin_1_13_4
  · exact nojoin_1_13_5
  · exact nojoin_1_13_6
  · exact nojoin_1_13_7
  · exact nojoin_1_14_0
  · exact nojoin_1_14_1
  · exact nojoin_1_14_2
  · exact nojoin_1_14_3
  · exact nojoin_1_14_4
  · exact nojoin_1_14_5
  · exact nojoin_1_14_6
  · exact nojoin_1_14_7
end SigGolfCandidate.Verify
