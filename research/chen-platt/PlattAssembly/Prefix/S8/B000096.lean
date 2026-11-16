import PlattAssemblyKernel
import PlattCertificates.Count131072.C073072
import PlattCertificates.Count131072.C073073
import PlattCertificates.Count131072.C073074
import PlattCertificates.Count131072.C073075
import PlattCertificates.Count131072.C073076
import PlattCertificates.Count131072.C073077
import PlattCertificates.Count131072.C073078
import PlattCertificates.Count131072.C073079
import PlattCertificates.Count131072.C073080
import PlattCertificates.Count131072.C073081
import PlattCertificates.Count131072.C073082
import PlattCertificates.Count131072.C073083
import PlattCertificates.Count131072.C073084
import PlattCertificates.Count131072.C073085
import PlattCertificates.Count131072.C073086
import PlattCertificates.Count131072.C073087
import PlattCertificates.Count131072.C073088
import PlattCertificates.Count131072.C073089
import PlattCertificates.Count131072.C073090
import PlattCertificates.Count131072.C073091
import PlattCertificates.Count131072.C073092
import PlattCertificates.Count131072.C073093
import PlattCertificates.Count131072.C073094
import PlattCertificates.Count131072.C073095
import PlattCertificates.Count131072.C073096
import PlattCertificates.Count131072.C073097
import PlattCertificates.Count131072.C073098
import PlattCertificates.Count131072.C073099
import PlattCertificates.Count131072.C073100
import PlattCertificates.Count131072.C073101
import PlattCertificates.Count131072.C073102
import PlattCertificates.Count131072.C073103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73072 : List PrefixCut := [⟨64,168003212,168003312⟩]
theorem checked73072 : checkPrefixCuts (2^48) 9581625345 10 Manual.Count131072.C073072.packed 64 cuts73072 = true := by
 decide +kernel
def cuts73073 : List PrefixCut := [⟨55,145322850,145322938⟩,
⟨64,168529696,168529796⟩]
theorem checked73073 : checkPrefixCuts (2^48) 9581756417 10 Manual.Count131072.C073073.packed 64 cuts73073 = true := by
 decide +kernel
def pointBounds73073 : List (Nat × Nat × Nat) := [(9581869056,116340337104716,116340726921803)]
theorem point_links_checked73073 : (cuts73073.take 1).map (fun c => (9581756417-1+2*2^10*c.k,116340191781866+c.lower,116340581598865+c.upper)) = pointBounds73073 := by
 decide +kernel
def cuts73074 : List PrefixCut := [⟨64,167499242,167499343⟩]
theorem checked73074 : checkPrefixCuts (2^48) 9581887489 10 Manual.Count131072.C073074.packed 64 cuts73074 = true := by
 decide +kernel
def cuts73075 : List PrefixCut := [⟨64,169230082,169230184⟩]
theorem checked73075 : checkPrefixCuts (2^48) 9582018561 10 Manual.Count131072.C073075.packed 64 cuts73075 = true := by
 decide +kernel
def cuts73076 : List PrefixCut := [⟨10,25938028,25938044⟩,
⟨64,168287770,168287872⟩]
theorem checked73076 : checkPrefixCuts (2^48) 9582149633 10 Manual.Count131072.C073076.packed 64 cuts73076 = true := by
 decide +kernel
def pointBounds73076 : List (Nat × Nat × Nat) := [(9582170112,116340722978914,116341112796232)]
theorem point_links_checked73076 : (cuts73076.take 1).map (fun c => (9582149633-1+2*2^10*c.k,116340697040886+c.lower,116341086858188+c.upper)) = pointBounds73076 := by
 decide +kernel
def cuts73077 : List PrefixCut := [⟨64,164525560,164525656⟩]
theorem checked73077 : checkPrefixCuts (2^48) 9582280705 10 Manual.Count131072.C073077.packed 64 cuts73077 = true := by
 decide +kernel
def cuts73078 : List PrefixCut := [⟨29,77283063,77283108⟩,
⟨64,170221850,170221952⟩]
theorem checked73078 : checkPrefixCuts (2^48) 9582411777 10 Manual.Count131072.C073078.packed 64 cuts73078 = true := by
 decide +kernel
def pointBounds73078 : List (Nat × Nat × Nat) := [(9582471168,116341107137279,116341496954824)]
theorem point_links_checked73078 : (cuts73078.take 1).map (fun c => (9582411777-1+2*2^10*c.k,116341029854216+c.lower,116341419671716+c.upper)) = pointBounds73078 := by
 decide +kernel
def cuts73079 : List PrefixCut := [⟨64,169367692,169367794⟩]
theorem checked73079 : checkPrefixCuts (2^48) 9582542849 10 Manual.Count131072.C073079.packed 64 cuts73079 = true := by
 decide +kernel
def cuts73080 : List PrefixCut := [⟨48,127097676,127097753⟩,
⟨64,169277251,169277355⟩]
theorem checked73080 : checkPrefixCuts (2^48) 9582673921 10 Manual.Count131072.C073080.packed 64 cuts73080 = true := by
 decide +kernel
def pointBounds73080 : List (Nat × Nat × Nat) := [(9582772224,116341496541434,116341886359215)]
theorem point_links_checked73080 : (cuts73080.take 1).map (fun c => (9582673921-1+2*2^10*c.k,116341369443758+c.lower,116341759261462+c.upper)) = pointBounds73080 := by
 decide +kernel
def cuts73081 : List PrefixCut := [⟨64,166425781,166425884⟩]
theorem checked73081 : checkPrefixCuts (2^48) 9582804993 10 Manual.Count131072.C073081.packed 64 cuts73081 = true := by
 decide +kernel
def cuts73082 : List PrefixCut := [⟨64,169096382,169096477⟩]
theorem checked73082 : checkPrefixCuts (2^48) 9582936065 10 Manual.Count131072.C073082.packed 64 cuts73082 = true := by
 decide +kernel
def cuts73083 : List PrefixCut := [⟨3,8018583,8018588⟩,
⟨64,169123456,169123553⟩]
theorem checked73083 : checkPrefixCuts (2^48) 9583067137 10 Manual.Count131072.C073083.packed 64 cuts73083 = true := by
 decide +kernel
def pointBounds73083 : List (Nat × Nat × Nat) := [(9583073280,116341882261755,116342272079766)]
theorem point_links_checked73083 : (cuts73083.take 1).map (fun c => (9583067137-1+2*2^10*c.k,116341874243172+c.lower,116342264061178+c.upper)) = pointBounds73083 := by
 decide +kernel
def cuts73084 : List PrefixCut := [⟨64,168357471,168357573⟩]
theorem checked73084 : checkPrefixCuts (2^48) 9583198209 10 Manual.Count131072.C073084.packed 64 cuts73084 = true := by
 decide +kernel
def cuts73085 : List PrefixCut := [⟨22,58654360,58654395⟩,
⟨64,168971965,168972070⟩]
theorem checked73085 : checkPrefixCuts (2^48) 9583329281 10 Manual.Count131072.C073085.packed 64 cuts73085 = true := by
 decide +kernel
def pointBounds73085 : List (Nat × Nat × Nat) := [(9583374336,116342270378459,116342660196699)]
theorem point_links_checked73085 : (cuts73085.take 1).map (fun c => (9583329281-1+2*2^10*c.k,116342211724099+c.lower,116342601542304+c.upper)) = pointBounds73085 := by
 decide +kernel
def cuts73086 : List PrefixCut := [⟨64,167119296,167119394⟩]
theorem checked73086 : checkPrefixCuts (2^48) 9583460353 10 Manual.Count131072.C073086.packed 64 cuts73086 = true := by
 decide +kernel
def cuts73087 : List PrefixCut := [⟨41,108934716,108934781⟩,
⟨64,167234510,167234608⟩]
theorem checked73087 : checkPrefixCuts (2^48) 9583591425 10 Manual.Count131072.C073087.packed 64 cuts73087 = true := by
 decide +kernel
def pointBounds73087 : List (Nat × Nat × Nat) := [(9583675392,116342656750076,116343046568549)]
theorem point_links_checked73087 : (cuts73087.take 1).map (fun c => (9583591425-1+2*2^10*c.k,116342547815360+c.lower,116342937633768+c.upper)) = pointBounds73087 := by
 decide +kernel
def cuts73088 : List PrefixCut := [⟨64,169229359,169229461⟩]
theorem checked73088 : checkPrefixCuts (2^48) 9583722497 10 Manual.Count131072.C073088.packed 64 cuts73088 = true := by
 decide +kernel
def cuts73089 : List PrefixCut := [⟨60,155599670,155599764⟩,
⟨64,166260730,166260829⟩]
theorem checked73089 : checkPrefixCuts (2^48) 9583853569 10 Manual.Count131072.C073089.packed 64 cuts73089 = true := by
 decide +kernel
def pointBounds73089 : List (Nat × Nat × Nat) := [(9583976448,116343039878899,116343429697601)]
theorem point_links_checked73089 : (cuts73089.take 1).map (fun c => (9583853569-1+2*2^10*c.k,116342884279229+c.lower,116343274097837+c.upper)) = pointBounds73089 := by
 decide +kernel
def cuts73090 : List PrefixCut := [⟨64,168226189,168226293⟩]
theorem checked73090 : checkPrefixCuts (2^48) 9583984641 10 Manual.Count131072.C073090.packed 64 cuts73090 = true := by
 decide +kernel
def cuts73091 : List PrefixCut := [⟨64,169369259,169369357⟩]
theorem checked73091 : checkPrefixCuts (2^48) 9584115713 10 Manual.Count131072.C073091.packed 64 cuts73091 = true := by
 decide +kernel
def cuts73092 : List PrefixCut := [⟨15,40322876,40322901⟩,
⟨64,168192217,168192319⟩]
theorem checked73092 : checkPrefixCuts (2^48) 9584246785 10 Manual.Count131072.C073092.packed 64 cuts73092 = true := by
 decide +kernel
def pointBounds73092 : List (Nat × Nat × Nat) := [(9584277504,116343428458283,116343818277217)]
theorem point_links_checked73092 : (cuts73092.take 1).map (fun c => (9584246785-1+2*2^10*c.k,116343388135407+c.lower,116343777954316+c.upper)) = pointBounds73092 := by
 decide +kernel
def cuts73093 : List PrefixCut := [⟨64,168043080,168043178⟩]
theorem checked73093 : checkPrefixCuts (2^48) 9584377857 10 Manual.Count131072.C073093.packed 64 cuts73093 = true := by
 decide +kernel
def cuts73094 : List PrefixCut := [⟨34,89483029,89483083⟩,
⟨64,167365330,167365430⟩]
theorem checked73094 : checkPrefixCuts (2^48) 9584508929 10 Manual.Count131072.C073094.packed 64 cuts73094 = true := by
 decide +kernel
def pointBounds73094 : List (Nat × Nat × Nat) := [(9584578560,116343813853733,116344203672896)]
theorem point_links_checked73094 : (cuts73094.take 1).map (fun c => (9584508929-1+2*2^10*c.k,116343724370704+c.lower,116344114189813+c.upper)) = pointBounds73094 := by
 decide +kernel
def cuts73095 : List PrefixCut := [⟨64,167039999,167040097⟩]
theorem checked73095 : checkPrefixCuts (2^48) 9584640001 10 Manual.Count131072.C073095.packed 64 cuts73095 = true := by
 decide +kernel
def cuts73096 : List PrefixCut := [⟨53,140343562,140343647⟩,
⟨64,167683793,167683895⟩]
theorem checked73096 : checkPrefixCuts (2^48) 9584771073 10 Manual.Count131072.C073096.packed 64 cuts73096 = true := by
 decide +kernel
def pointBounds73096 : List (Nat × Nat × Nat) := [(9584879616,116344199119595,116344588938987)]
theorem point_links_checked73096 : (cuts73096.take 1).map (fun c => (9584771073-1+2*2^10*c.k,116344058776033+c.lower,116344448595340+c.upper)) = pointBounds73096 := by
 decide +kernel
def cuts73097 : List PrefixCut := [⟨64,167299721,167299831⟩]
theorem checked73097 : checkPrefixCuts (2^48) 9584902145 10 Manual.Count131072.C073097.packed 64 cuts73097 = true := by
 decide +kernel
def cuts73098 : List PrefixCut := [⟨64,167385530,167385641⟩]
theorem checked73098 : checkPrefixCuts (2^48) 9585033217 10 Manual.Count131072.C073098.packed 64 cuts73098 = true := by
 decide +kernel
def cuts73099 : List PrefixCut := [⟨8,20644059,20644069⟩,
⟨64,166032431,166032530⟩]
theorem checked73099 : checkPrefixCuts (2^48) 9585164289 10 Manual.Count131072.C073099.packed 64 cuts73099 = true := by
 decide +kernel
def pointBounds73099 : List (Nat × Nat × Nat) := [(9585180672,116344581789136,116344971608776)]
theorem point_links_checked73099 : (cuts73099.take 1).map (fun c => (9585164289-1+2*2^10*c.k,116344561145077+c.lower,116344950964707+c.upper)) = pointBounds73099 := by
 decide +kernel
def cuts73100 : List PrefixCut := [⟨64,165119859,165119958⟩]
theorem checked73100 : checkPrefixCuts (2^48) 9585295361 10 Manual.Count131072.C073100.packed 64 cuts73100 = true := by
 decide +kernel
def cuts73101 : List PrefixCut := [⟨27,68508066,68508109⟩,
⟨64,165792969,165793070⟩]
theorem checked73101 : checkPrefixCuts (2^48) 9585426433 10 Manual.Count131072.C073101.packed 64 cuts73101 = true := by
 decide +kernel
def pointBounds73101 : List (Nat × Nat × Nat) := [(9585481728,116344960805433,116345350625304)]
theorem point_links_checked73101 : (cuts73101.take 1).map (fun c => (9585426433-1+2*2^10*c.k,116344892297367+c.lower,116345282117195+c.upper)) = pointBounds73101 := by
 decide +kernel
def cuts73102 : List PrefixCut := [⟨64,166583552,166583652⟩]
theorem checked73102 : checkPrefixCuts (2^48) 9585557505 10 Manual.Count131072.C073102.packed 64 cuts73102 = true := by
 decide +kernel
def cuts73103 : List PrefixCut := [⟨46,119364387,119364460⟩,
⟨64,168607368,168607469⟩]
theorem checked73103 : checkPrefixCuts (2^48) 9585688577 10 Manual.Count131072.C073103.packed 64 cuts73103 = true := by
 decide +kernel
def pointBounds73103 : List (Nat × Nat × Nat) := [(9585782784,116345344038275,116345733858377)]
theorem point_links_checked73103 : (cuts73103.take 1).map (fun c => (9585688577-1+2*2^10*c.k,116345224673888+c.lower,116345614493917+c.upper)) = pointBounds73103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000096
