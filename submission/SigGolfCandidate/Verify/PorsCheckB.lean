import SigGolfCandidate.Verify.PorsCheckA
import Mathlib.Tactic.IntervalCases

/-! Kernel check of the PORS code blocks: prologue and setup, leaves, dispatches, entry tails,
ladder positions, tails. -/

set_option Elab.async false

namespace SigGolfCandidate.Verify

theorem startCheck_ok : startCheck = true := by decide +kernel
theorem leafCheck_all : (List.range 15).all leafCheck = true := by decide +kernel
theorem dispCheck_all : (List.range 210).all dispCheck = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hb : c < 210 := List.mem_range.mp hc
  interval_cases c <;> decide +kernel
theorem pentCheck_ok : pentCheck = true := by decide +kernel
theorem posCheck_0 : posCheck 0 = true := by decide +kernel
theorem posCheck_1 : posCheck 1 = true := by decide +kernel
theorem posCheck_2 : posCheck 2 = true := by decide +kernel
theorem prefixCheck_0 : prefixCheck 0 = true := by
  unfold prefixCheck
  apply List.all_eq_true.mpr
  intro a ha
  have hb : 3 ≤ a ∧ a < 15 := by
    simpa only [Nat.reduceAdd] using (List.mem_range'_1.mp ha)
  rcases hb with ⟨hlo, hhi⟩
  interval_cases a <;> decide +kernel
theorem prefixCheck_1 : prefixCheck 1 = true := by
  unfold prefixCheck
  apply List.all_eq_true.mpr
  intro a ha
  have hb : 3 ≤ a ∧ a < 15 := by
    simpa only [Nat.reduceAdd] using (List.mem_range'_1.mp ha)
  rcases hb with ⟨hlo, hhi⟩
  interval_cases a <;> decide +kernel
theorem prefixCheck_2 : prefixCheck 2 = true := by
  unfold prefixCheck
  apply List.all_eq_true.mpr
  intro a ha
  have hb : 3 ≤ a ∧ a < 15 := by
    simpa only [Nat.reduceAdd] using (List.mem_range'_1.mp ha)
  rcases hb with ⟨hlo, hhi⟩
  interval_cases a <;> decide +kernel
private def nojoinCheckAt (V a : Nat) : Bool :=
  (List.range 8).all fun bits =>
    (List.range a).all fun i => i < prefixN a ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=a && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc V t a i bits) (posDirs t (14-a+i) t'))
          (prefixPosSpec V t a i bits t') (posObl (14-a+i)) posKnown posKeep

private theorem nojoin_0_3 : nojoinCheckAt 0 3 = true := by decide +kernel
private theorem nojoin_0_4 : nojoinCheckAt 0 4 = true := by decide +kernel
private theorem nojoin_0_5 : nojoinCheckAt 0 5 = true := by decide +kernel
private theorem nojoin_0_6 : nojoinCheckAt 0 6 = true := by decide +kernel
private theorem nojoin_0_7 : nojoinCheckAt 0 7 = true := by decide +kernel
private theorem nojoin_0_8 : nojoinCheckAt 0 8 = true := by decide +kernel
private theorem nojoin_0_9 : nojoinCheckAt 0 9 = true := by decide +kernel
private theorem nojoin_0_10 : nojoinCheckAt 0 10 = true := by decide +kernel
private theorem nojoin_0_11 : nojoinCheckAt 0 11 = true := by decide +kernel
private theorem nojoin_0_12 : nojoinCheckAt 0 12 = true := by decide +kernel
private theorem nojoin_0_13 : nojoinCheckAt 0 13 = true := by decide +kernel
private theorem nojoin_0_14 : nojoinCheckAt 0 14 = true := by decide +kernel
theorem nojoinCheck_0 : nojoinCheck 0 = true := by
  change (List.range' 3 12).all (nojoinCheckAt 0) = true
  apply List.all_eq_true.mpr
  intro a ha
  have hb : 3 ≤ a ∧ a < 15 := by
    simpa only [Nat.reduceAdd] using (List.mem_range'_1.mp ha)
  rcases hb with ⟨hlo, hhi⟩
  interval_cases a
  · exact nojoin_0_3
  · exact nojoin_0_4
  · exact nojoin_0_5
  · exact nojoin_0_6
  · exact nojoin_0_7
  · exact nojoin_0_8
  · exact nojoin_0_9
  · exact nojoin_0_10
  · exact nojoin_0_11
  · exact nojoin_0_12
  · exact nojoin_0_13
  · exact nojoin_0_14

private theorem nojoin_1_3 : nojoinCheckAt 1 3 = true := by decide +kernel
private theorem nojoin_1_4 : nojoinCheckAt 1 4 = true := by decide +kernel
private theorem nojoin_1_5 : nojoinCheckAt 1 5 = true := by decide +kernel
private theorem nojoin_1_6 : nojoinCheckAt 1 6 = true := by decide +kernel
private theorem nojoin_1_7 : nojoinCheckAt 1 7 = true := by decide +kernel
private theorem nojoin_1_8 : nojoinCheckAt 1 8 = true := by decide +kernel
private theorem nojoin_1_9 : nojoinCheckAt 1 9 = true := by decide +kernel
private theorem nojoin_1_10 : nojoinCheckAt 1 10 = true := by decide +kernel
private theorem nojoin_1_11 : nojoinCheckAt 1 11 = true := by decide +kernel
private theorem nojoin_1_12 : nojoinCheckAt 1 12 = true := by decide +kernel
private theorem nojoin_1_13 : nojoinCheckAt 1 13 = true := by decide +kernel
private theorem nojoin_1_14 : nojoinCheckAt 1 14 = true := by decide +kernel
theorem nojoinCheck_1 : nojoinCheck 1 = true := by
  change (List.range' 3 12).all (nojoinCheckAt 1) = true
  apply List.all_eq_true.mpr
  intro a ha
  have hb : 3 ≤ a ∧ a < 15 := by
    simpa only [Nat.reduceAdd] using (List.mem_range'_1.mp ha)
  rcases hb with ⟨hlo, hhi⟩
  interval_cases a
  · exact nojoin_1_3
  · exact nojoin_1_4
  · exact nojoin_1_5
  · exact nojoin_1_6
  · exact nojoin_1_7
  · exact nojoin_1_8
  · exact nojoin_1_9
  · exact nojoin_1_10
  · exact nojoin_1_11
  · exact nojoin_1_12
  · exact nojoin_1_13
  · exact nojoin_1_14

private theorem tailCheck_0 : tailCheck 0 = true := by decide +kernel
private theorem tailCheck_1 : tailCheck 1 = true := by decide +kernel
private theorem tailCheck_2 : tailCheck 2 = true := by decide +kernel
private theorem tailCheck_3 : tailCheck 3 = true := by decide +kernel
private theorem tailCheck_4 : tailCheck 4 = true := by decide +kernel
private theorem tailCheck_5 : tailCheck 5 = true := by decide +kernel
private theorem tailCheck_6 : tailCheck 6 = true := by decide +kernel
private theorem tailCheck_7 : tailCheck 7 = true := by decide +kernel
private theorem tailCheck_8 : tailCheck 8 = true := by decide +kernel
private theorem tailCheck_9 : tailCheck 9 = true := by decide +kernel
private theorem tailCheck_10 : tailCheck 10 = true := by decide +kernel
private theorem tailCheck_11 : tailCheck 11 = true := by decide +kernel
private theorem tailCheck_12 : tailCheck 12 = true := by decide +kernel
private theorem tailCheck_13 : tailCheck 13 = true := by decide +kernel
private theorem tailCheck_14 : tailCheck 14 = true := by decide +kernel
private theorem tailCheck_15 : tailCheck 15 = true := by decide +kernel
private theorem tailCheck_16 : tailCheck 16 = true := by decide +kernel
private theorem tailCheck_17 : tailCheck 17 = true := by decide +kernel
private theorem tailCheck_18 : tailCheck 18 = true := by decide +kernel
private theorem tailCheck_19 : tailCheck 19 = true := by decide +kernel
private theorem tailCheck_20 : tailCheck 20 = true := by decide +kernel
private theorem tailCheck_21 : tailCheck 21 = true := by decide +kernel
private theorem tailCheck_22 : tailCheck 22 = true := by decide +kernel
private theorem tailCheck_23 : tailCheck 23 = true := by decide +kernel
private theorem tailCheck_24 : tailCheck 24 = true := by decide +kernel
private theorem tailCheck_25 : tailCheck 25 = true := by decide +kernel
private theorem tailCheck_26 : tailCheck 26 = true := by decide +kernel
private theorem tailCheck_27 : tailCheck 27 = true := by decide +kernel
private theorem tailCheck_28 : tailCheck 28 = true := by decide +kernel
private theorem tailCheck_29 : tailCheck 29 = true := by decide +kernel
private theorem tailCheck_30 : tailCheck 30 = true := by decide +kernel
private theorem tailCheck_31 : tailCheck 31 = true := by decide +kernel
private theorem tailCheck_32 : tailCheck 32 = true := by decide +kernel
private theorem tailCheck_33 : tailCheck 33 = true := by decide +kernel
private theorem tailCheck_34 : tailCheck 34 = true := by decide +kernel
private theorem tailCheck_35 : tailCheck 35 = true := by decide +kernel
private theorem tailCheck_36 : tailCheck 36 = true := by decide +kernel
private theorem tailCheck_37 : tailCheck 37 = true := by decide +kernel
private theorem tailCheck_38 : tailCheck 38 = true := by decide +kernel
private theorem tailCheck_39 : tailCheck 39 = true := by decide +kernel
private theorem tailCheck_40 : tailCheck 40 = true := by decide +kernel
private theorem tailCheck_41 : tailCheck 41 = true := by decide +kernel
private theorem tailCheck_42 : tailCheck 42 = true := by decide +kernel
private theorem tailCheck_43 : tailCheck 43 = true := by decide +kernel
private theorem tailCheck_44 : tailCheck 44 = true := by decide +kernel
private theorem tailCheck_45 : tailCheck 45 = true := by decide +kernel
private theorem tailCheck_46 : tailCheck 46 = true := by decide +kernel
private theorem tailCheck_47 : tailCheck 47 = true := by decide +kernel
private theorem tailCheck_48 : tailCheck 48 = true := by decide +kernel
private theorem tailCheck_49 : tailCheck 49 = true := by decide +kernel
private theorem tailCheck_50 : tailCheck 50 = true := by decide +kernel
private theorem tailCheck_51 : tailCheck 51 = true := by decide +kernel
private theorem tailCheck_52 : tailCheck 52 = true := by decide +kernel
private theorem tailCheck_53 : tailCheck 53 = true := by decide +kernel
private theorem tailCheck_54 : tailCheck 54 = true := by decide +kernel
private theorem tailCheck_55 : tailCheck 55 = true := by decide +kernel
private theorem tailCheck_56 : tailCheck 56 = true := by decide +kernel
private theorem tailCheck_57 : tailCheck 57 = true := by decide +kernel
private theorem tailCheck_58 : tailCheck 58 = true := by decide +kernel
private theorem tailCheck_59 : tailCheck 59 = true := by decide +kernel
private theorem tailCheck_60 : tailCheck 60 = true := by decide +kernel
private theorem tailCheck_61 : tailCheck 61 = true := by decide +kernel
private theorem tailCheck_62 : tailCheck 62 = true := by decide +kernel
private theorem tailCheck_63 : tailCheck 63 = true := by decide +kernel
private theorem tailCheck_64 : tailCheck 64 = true := by decide +kernel
private theorem tailCheck_65 : tailCheck 65 = true := by decide +kernel
private theorem tailCheck_66 : tailCheck 66 = true := by decide +kernel
private theorem tailCheck_67 : tailCheck 67 = true := by decide +kernel
private theorem tailCheck_68 : tailCheck 68 = true := by decide +kernel
private theorem tailCheck_69 : tailCheck 69 = true := by decide +kernel
private theorem tailCheck_70 : tailCheck 70 = true := by decide +kernel
private theorem tailCheck_71 : tailCheck 71 = true := by decide +kernel
private theorem tailCheck_72 : tailCheck 72 = true := by decide +kernel
private theorem tailCheck_73 : tailCheck 73 = true := by decide +kernel
private theorem tailCheck_74 : tailCheck 74 = true := by decide +kernel
private theorem tailCheck_75 : tailCheck 75 = true := by decide +kernel
private theorem tailCheck_76 : tailCheck 76 = true := by decide +kernel
private theorem tailCheck_77 : tailCheck 77 = true := by decide +kernel
private theorem tailCheck_78 : tailCheck 78 = true := by decide +kernel
private theorem tailCheck_79 : tailCheck 79 = true := by decide +kernel
private theorem tailCheck_80 : tailCheck 80 = true := by decide +kernel
private theorem tailCheck_81 : tailCheck 81 = true := by decide +kernel
private theorem tailCheck_82 : tailCheck 82 = true := by decide +kernel
private theorem tailCheck_83 : tailCheck 83 = true := by decide +kernel
private theorem tailCheck_84 : tailCheck 84 = true := by decide +kernel
private theorem tailCheck_85 : tailCheck 85 = true := by decide +kernel
private theorem tailCheck_86 : tailCheck 86 = true := by decide +kernel
private theorem tailCheck_87 : tailCheck 87 = true := by decide +kernel
private theorem tailCheck_88 : tailCheck 88 = true := by decide +kernel
private theorem tailCheck_89 : tailCheck 89 = true := by decide +kernel
private theorem tailCheck_90 : tailCheck 90 = true := by decide +kernel
private theorem tailCheck_91 : tailCheck 91 = true := by decide +kernel
private theorem tailCheck_92 : tailCheck 92 = true := by decide +kernel
private theorem tailCheck_93 : tailCheck 93 = true := by decide +kernel
private theorem tailCheck_94 : tailCheck 94 = true := by decide +kernel
private theorem tailCheck_95 : tailCheck 95 = true := by decide +kernel
private theorem tailCheck_96 : tailCheck 96 = true := by decide +kernel
private theorem tailCheck_97 : tailCheck 97 = true := by decide +kernel
private theorem tailCheck_98 : tailCheck 98 = true := by decide +kernel
private theorem tailCheck_99 : tailCheck 99 = true := by decide +kernel
private theorem tailCheck_100 : tailCheck 100 = true := by decide +kernel
private theorem tailCheck_101 : tailCheck 101 = true := by decide +kernel
private theorem tailCheck_102 : tailCheck 102 = true := by decide +kernel
private theorem tailCheck_103 : tailCheck 103 = true := by decide +kernel
private theorem tailCheck_104 : tailCheck 104 = true := by decide +kernel
private theorem tailCheck_105 : tailCheck 105 = true := by decide +kernel
private theorem tailCheck_106 : tailCheck 106 = true := by decide +kernel
private theorem tailCheck_107 : tailCheck 107 = true := by decide +kernel
private theorem tailCheck_108 : tailCheck 108 = true := by decide +kernel
private theorem tailCheck_109 : tailCheck 109 = true := by decide +kernel
private theorem tailCheck_110 : tailCheck 110 = true := by decide +kernel
private theorem tailCheck_111 : tailCheck 111 = true := by decide +kernel
private theorem tailCheck_112 : tailCheck 112 = true := by decide +kernel
private theorem tailCheck_113 : tailCheck 113 = true := by decide +kernel
private theorem tailCheck_114 : tailCheck 114 = true := by decide +kernel
private theorem tailCheck_115 : tailCheck 115 = true := by decide +kernel
private theorem tailCheck_116 : tailCheck 116 = true := by decide +kernel
private theorem tailCheck_117 : tailCheck 117 = true := by decide +kernel
private theorem tailCheck_118 : tailCheck 118 = true := by decide +kernel
private theorem tailCheck_119 : tailCheck 119 = true := by decide +kernel
private theorem tailCheck_120 : tailCheck 120 = true := by decide +kernel
private theorem tailCheck_121 : tailCheck 121 = true := by decide +kernel
private theorem tailCheck_122 : tailCheck 122 = true := by decide +kernel
private theorem tailCheck_123 : tailCheck 123 = true := by decide +kernel
private theorem tailCheck_124 : tailCheck 124 = true := by decide +kernel
private theorem tailCheck_125 : tailCheck 125 = true := by decide +kernel
private theorem tailCheck_126 : tailCheck 126 = true := by decide +kernel
private theorem tailCheck_127 : tailCheck 127 = true := by decide +kernel
private theorem tailCheck_128 : tailCheck 128 = true := by decide +kernel
private theorem tailCheck_129 : tailCheck 129 = true := by decide +kernel
private theorem tailCheck_130 : tailCheck 130 = true := by decide +kernel
private theorem tailCheck_131 : tailCheck 131 = true := by decide +kernel
private theorem tailCheck_132 : tailCheck 132 = true := by decide +kernel
private theorem tailCheck_133 : tailCheck 133 = true := by decide +kernel
private theorem tailCheck_134 : tailCheck 134 = true := by decide +kernel
private theorem tailCheck_135 : tailCheck 135 = true := by decide +kernel
private theorem tailCheck_136 : tailCheck 136 = true := by decide +kernel
private theorem tailCheck_137 : tailCheck 137 = true := by decide +kernel
private theorem tailCheck_138 : tailCheck 138 = true := by decide +kernel
private theorem tailCheck_139 : tailCheck 139 = true := by decide +kernel
private theorem tailCheck_140 : tailCheck 140 = true := by decide +kernel
private theorem tailCheck_141 : tailCheck 141 = true := by decide +kernel
private theorem tailCheck_142 : tailCheck 142 = true := by decide +kernel
private theorem tailCheck_143 : tailCheck 143 = true := by decide +kernel
private theorem tailCheck_144 : tailCheck 144 = true := by decide +kernel
private theorem tailCheck_145 : tailCheck 145 = true := by decide +kernel
private theorem tailCheck_146 : tailCheck 146 = true := by decide +kernel
private theorem tailCheck_147 : tailCheck 147 = true := by decide +kernel
private theorem tailCheck_148 : tailCheck 148 = true := by decide +kernel
private theorem tailCheck_149 : tailCheck 149 = true := by decide +kernel
private theorem tailCheck_150 : tailCheck 150 = true := by decide +kernel
private theorem tailCheck_151 : tailCheck 151 = true := by decide +kernel
private theorem tailCheck_152 : tailCheck 152 = true := by decide +kernel
private theorem tailCheck_153 : tailCheck 153 = true := by decide +kernel
private theorem tailCheck_154 : tailCheck 154 = true := by decide +kernel
private theorem tailCheck_155 : tailCheck 155 = true := by decide +kernel
private theorem tailCheck_156 : tailCheck 156 = true := by decide +kernel
private theorem tailCheck_157 : tailCheck 157 = true := by decide +kernel
private theorem tailCheck_158 : tailCheck 158 = true := by decide +kernel
private theorem tailCheck_159 : tailCheck 159 = true := by decide +kernel
private theorem tailCheck_160 : tailCheck 160 = true := by decide +kernel
private theorem tailCheck_161 : tailCheck 161 = true := by decide +kernel
private theorem tailCheck_162 : tailCheck 162 = true := by decide +kernel
private theorem tailCheck_163 : tailCheck 163 = true := by decide +kernel
private theorem tailCheck_164 : tailCheck 164 = true := by decide +kernel
private theorem tailCheck_165 : tailCheck 165 = true := by decide +kernel
private theorem tailCheck_166 : tailCheck 166 = true := by decide +kernel
private theorem tailCheck_167 : tailCheck 167 = true := by decide +kernel
private theorem tailCheck_168 : tailCheck 168 = true := by decide +kernel
private theorem tailCheck_169 : tailCheck 169 = true := by decide +kernel
private theorem tailCheck_170 : tailCheck 170 = true := by decide +kernel
private theorem tailCheck_171 : tailCheck 171 = true := by decide +kernel
private theorem tailCheck_172 : tailCheck 172 = true := by decide +kernel
private theorem tailCheck_173 : tailCheck 173 = true := by decide +kernel
private theorem tailCheck_174 : tailCheck 174 = true := by decide +kernel
private theorem tailCheck_175 : tailCheck 175 = true := by decide +kernel
private theorem tailCheck_176 : tailCheck 176 = true := by decide +kernel
private theorem tailCheck_177 : tailCheck 177 = true := by decide +kernel
private theorem tailCheck_178 : tailCheck 178 = true := by decide +kernel
private theorem tailCheck_179 : tailCheck 179 = true := by decide +kernel
private theorem tailCheck_180 : tailCheck 180 = true := by decide +kernel
private theorem tailCheck_181 : tailCheck 181 = true := by decide +kernel
private theorem tailCheck_182 : tailCheck 182 = true := by decide +kernel
private theorem tailCheck_183 : tailCheck 183 = true := by decide +kernel
private theorem tailCheck_184 : tailCheck 184 = true := by decide +kernel
private theorem tailCheck_185 : tailCheck 185 = true := by decide +kernel
private theorem tailCheck_186 : tailCheck 186 = true := by decide +kernel
private theorem tailCheck_187 : tailCheck 187 = true := by decide +kernel
private theorem tailCheck_188 : tailCheck 188 = true := by decide +kernel
private theorem tailCheck_189 : tailCheck 189 = true := by decide +kernel
private theorem tailCheck_190 : tailCheck 190 = true := by decide +kernel
private theorem tailCheck_191 : tailCheck 191 = true := by decide +kernel
private theorem tailCheck_192 : tailCheck 192 = true := by decide +kernel
private theorem tailCheck_193 : tailCheck 193 = true := by decide +kernel
private theorem tailCheck_194 : tailCheck 194 = true := by decide +kernel
theorem tailCheck_all : (List.range 195).all tailCheck = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hb : c < 195 := List.mem_range.mp hc
  interval_cases c
  · exact tailCheck_0
  · exact tailCheck_1
  · exact tailCheck_2
  · exact tailCheck_3
  · exact tailCheck_4
  · exact tailCheck_5
  · exact tailCheck_6
  · exact tailCheck_7
  · exact tailCheck_8
  · exact tailCheck_9
  · exact tailCheck_10
  · exact tailCheck_11
  · exact tailCheck_12
  · exact tailCheck_13
  · exact tailCheck_14
  · exact tailCheck_15
  · exact tailCheck_16
  · exact tailCheck_17
  · exact tailCheck_18
  · exact tailCheck_19
  · exact tailCheck_20
  · exact tailCheck_21
  · exact tailCheck_22
  · exact tailCheck_23
  · exact tailCheck_24
  · exact tailCheck_25
  · exact tailCheck_26
  · exact tailCheck_27
  · exact tailCheck_28
  · exact tailCheck_29
  · exact tailCheck_30
  · exact tailCheck_31
  · exact tailCheck_32
  · exact tailCheck_33
  · exact tailCheck_34
  · exact tailCheck_35
  · exact tailCheck_36
  · exact tailCheck_37
  · exact tailCheck_38
  · exact tailCheck_39
  · exact tailCheck_40
  · exact tailCheck_41
  · exact tailCheck_42
  · exact tailCheck_43
  · exact tailCheck_44
  · exact tailCheck_45
  · exact tailCheck_46
  · exact tailCheck_47
  · exact tailCheck_48
  · exact tailCheck_49
  · exact tailCheck_50
  · exact tailCheck_51
  · exact tailCheck_52
  · exact tailCheck_53
  · exact tailCheck_54
  · exact tailCheck_55
  · exact tailCheck_56
  · exact tailCheck_57
  · exact tailCheck_58
  · exact tailCheck_59
  · exact tailCheck_60
  · exact tailCheck_61
  · exact tailCheck_62
  · exact tailCheck_63
  · exact tailCheck_64
  · exact tailCheck_65
  · exact tailCheck_66
  · exact tailCheck_67
  · exact tailCheck_68
  · exact tailCheck_69
  · exact tailCheck_70
  · exact tailCheck_71
  · exact tailCheck_72
  · exact tailCheck_73
  · exact tailCheck_74
  · exact tailCheck_75
  · exact tailCheck_76
  · exact tailCheck_77
  · exact tailCheck_78
  · exact tailCheck_79
  · exact tailCheck_80
  · exact tailCheck_81
  · exact tailCheck_82
  · exact tailCheck_83
  · exact tailCheck_84
  · exact tailCheck_85
  · exact tailCheck_86
  · exact tailCheck_87
  · exact tailCheck_88
  · exact tailCheck_89
  · exact tailCheck_90
  · exact tailCheck_91
  · exact tailCheck_92
  · exact tailCheck_93
  · exact tailCheck_94
  · exact tailCheck_95
  · exact tailCheck_96
  · exact tailCheck_97
  · exact tailCheck_98
  · exact tailCheck_99
  · exact tailCheck_100
  · exact tailCheck_101
  · exact tailCheck_102
  · exact tailCheck_103
  · exact tailCheck_104
  · exact tailCheck_105
  · exact tailCheck_106
  · exact tailCheck_107
  · exact tailCheck_108
  · exact tailCheck_109
  · exact tailCheck_110
  · exact tailCheck_111
  · exact tailCheck_112
  · exact tailCheck_113
  · exact tailCheck_114
  · exact tailCheck_115
  · exact tailCheck_116
  · exact tailCheck_117
  · exact tailCheck_118
  · exact tailCheck_119
  · exact tailCheck_120
  · exact tailCheck_121
  · exact tailCheck_122
  · exact tailCheck_123
  · exact tailCheck_124
  · exact tailCheck_125
  · exact tailCheck_126
  · exact tailCheck_127
  · exact tailCheck_128
  · exact tailCheck_129
  · exact tailCheck_130
  · exact tailCheck_131
  · exact tailCheck_132
  · exact tailCheck_133
  · exact tailCheck_134
  · exact tailCheck_135
  · exact tailCheck_136
  · exact tailCheck_137
  · exact tailCheck_138
  · exact tailCheck_139
  · exact tailCheck_140
  · exact tailCheck_141
  · exact tailCheck_142
  · exact tailCheck_143
  · exact tailCheck_144
  · exact tailCheck_145
  · exact tailCheck_146
  · exact tailCheck_147
  · exact tailCheck_148
  · exact tailCheck_149
  · exact tailCheck_150
  · exact tailCheck_151
  · exact tailCheck_152
  · exact tailCheck_153
  · exact tailCheck_154
  · exact tailCheck_155
  · exact tailCheck_156
  · exact tailCheck_157
  · exact tailCheck_158
  · exact tailCheck_159
  · exact tailCheck_160
  · exact tailCheck_161
  · exact tailCheck_162
  · exact tailCheck_163
  · exact tailCheck_164
  · exact tailCheck_165
  · exact tailCheck_166
  · exact tailCheck_167
  · exact tailCheck_168
  · exact tailCheck_169
  · exact tailCheck_170
  · exact tailCheck_171
  · exact tailCheck_172
  · exact tailCheck_173
  · exact tailCheck_174
  · exact tailCheck_175
  · exact tailCheck_176
  · exact tailCheck_177
  · exact tailCheck_178
  · exact tailCheck_179
  · exact tailCheck_180
  · exact tailCheck_181
  · exact tailCheck_182
  · exact tailCheck_183
  · exact tailCheck_184
  · exact tailCheck_185
  · exact tailCheck_186
  · exact tailCheck_187
  · exact tailCheck_188
  · exact tailCheck_189
  · exact tailCheck_190
  · exact tailCheck_191
  · exact tailCheck_192
  · exact tailCheck_193
  · exact tailCheck_194

theorem tailFCheck_all : (List.range 3).all tailFCheck = true := by decide +kernel

end SigGolfCandidate.Verify
