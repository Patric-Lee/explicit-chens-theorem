import PlattAssemblyKernel
import PlattCertificates.Count131072.C040064
import PlattCertificates.Count131072.C040065
import PlattCertificates.Count131072.C040066
import PlattCertificates.Count131072.C040067
import PlattCertificates.Count131072.C040068
import PlattCertificates.Count131072.C040069
import PlattCertificates.Count131072.C040070
import PlattCertificates.Count131072.C040071
import PlattCertificates.Count131072.C040072
import PlattCertificates.Count131072.C040073
import PlattCertificates.Count131072.C040074
import PlattCertificates.Count131072.C040075
import PlattCertificates.Count131072.C040076
import PlattCertificates.Count131072.C040077
import PlattCertificates.Count131072.C040078
import PlattCertificates.Count131072.C040079
import PlattCertificates.Count131072.C040080
import PlattCertificates.Count131072.C040081
import PlattCertificates.Count131072.C040082
import PlattCertificates.Count131072.C040083
import PlattCertificates.Count131072.C040084
import PlattCertificates.Count131072.C040085
import PlattCertificates.Count131072.C040086
import PlattCertificates.Count131072.C040087
import PlattCertificates.Count131072.C040088
import PlattCertificates.Count131072.C040089
import PlattCertificates.Count131072.C040090
import PlattCertificates.Count131072.C040091
import PlattCertificates.Count131072.C040092
import PlattCertificates.Count131072.C040093
import PlattCertificates.Count131072.C040094
import PlattCertificates.Count131072.C040095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40064 : List PrefixCut := [⟨62,305134509,305134691⟩,
⟨64,315096649,315096837⟩]
theorem checked40064 : checkPrefixCuts (2^48) 5255200769 10 Manual.Count131072.C040064.packed 64 cuts40064 = true := by
 decide +kernel
def pointBounds40064 : List (Nat × Nat × Nat) := [(5255327744,108886615334505,108887000852201)]
theorem point_links_checked40064 : (cuts40064.take 1).map (fun c => (5255200769-1+2*2^10*c.k,108886310199996+c.lower,108886695717510+c.upper)) = pointBounds40064 := by
 decide +kernel
def cuts40065 : List PrefixCut := [⟨64,316695608,316695795⟩]
theorem checked40065 : checkPrefixCuts (2^48) 5255331841 10 Manual.Count131072.C040065.packed 64 cuts40065 = true := by
 decide +kernel
def cuts40066 : List PrefixCut := [⟨15,73964114,73964158⟩,
⟨64,313956207,313956395⟩]
theorem checked40066 : checkPrefixCuts (2^48) 5255462913 10 Manual.Count131072.C040066.packed 64 cuts40066 = true := by
 decide +kernel
def pointBounds40066 : List (Nat × Nat × Nat) := [(5255493632,108887015956367,108887401474300)]
theorem point_links_checked40066 : (cuts40066.take 1).map (fun c => (5255462913-1+2*2^10*c.k,108886941992253+c.lower,108887327510142+c.upper)) = pointBounds40066 := by
 decide +kernel
def cuts40067 : List PrefixCut := [⟨32,153440427,153440516⟩,
⟨64,313252122,313252308⟩]
theorem checked40067 : checkPrefixCuts (2^48) 5255593985 10 Manual.Count131072.C040067.packed 64 cuts40067 = true := by
 decide +kernel
def pointBounds40067 : List (Nat × Nat × Nat) := [(5255659520,108887409388887,108887794907053)]
theorem point_links_checked40067 : (cuts40067.take 1).map (fun c => (5255593985-1+2*2^10*c.k,108887255948460+c.lower,108887641466537+c.upper)) = pointBounds40067 := by
 decide +kernel
def cuts40068 : List PrefixCut := [⟨49,237196668,237196810⟩,
⟨64,311369900,311370087⟩]
theorem checked40068 : checkPrefixCuts (2^48) 5255725057 10 Manual.Count131072.C040068.packed 64 cuts40068 = true := by
 decide +kernel
def pointBounds40068 : List (Nat × Nat × Nat) := [(5255825408,108887806397250,108888191915655)]
theorem point_links_checked40068 : (cuts40068.take 1).map (fun c => (5255725057-1+2*2^10*c.k,108887569200582+c.lower,108887954718845+c.upper)) = pointBounds40068 := by
 decide +kernel
def cuts40069 : List PrefixCut := [⟨64,312486770,312486948⟩]
theorem checked40069 : checkPrefixCuts (2^48) 5255856129 10 Manual.Count131072.C040069.packed 64 cuts40069 = true := by
 decide +kernel
def cuts40070 : List PrefixCut := [⟨2,9104039,9104044⟩,
⟨64,312907388,312907579⟩]
theorem checked40070 : checkPrefixCuts (2^48) 5255987201 10 Manual.Count131072.C040070.packed 64 cuts40070 = true := by
 decide +kernel
def pointBounds40070 : List (Nat × Nat × Nat) := [(5255991296,108888202161291,108888587679924)]
theorem point_links_checked40070 : (cuts40070.take 1).map (fun c => (5255987201-1+2*2^10*c.k,108888193057252+c.lower,108888578575880+c.upper)) = pointBounds40070 := by
 decide +kernel
def cuts40071 : List PrefixCut := [⟨19,93554748,93554804⟩,
⟨64,310114945,310115131⟩]
theorem checked40071 : checkPrefixCuts (2^48) 5256118273 10 Manual.Count131072.C040071.packed 64 cuts40071 = true := by
 decide +kernel
def pointBounds40071 : List (Nat × Nat × Nat) := [(5256157184,108888599519388,108888985038263)]
theorem point_links_checked40071 : (cuts40071.take 1).map (fun c => (5256118273-1+2*2^10*c.k,108888505964640+c.lower,108888891483459+c.upper)) = pointBounds40071 := by
 decide +kernel
def cuts40072 : List PrefixCut := [⟨36,175108973,175109078⟩,
⟨64,311767237,311767423⟩]
theorem checked40072 : checkPrefixCuts (2^48) 5256249345 10 Manual.Count131072.C040072.packed 64 cuts40072 = true := by
 decide +kernel
def pointBounds40072 : List (Nat × Nat × Nat) := [(5256323072,108888991188558,108889376707668)]
theorem point_links_checked40072 : (cuts40072.take 1).map (fun c => (5256249345-1+2*2^10*c.k,108888816079585+c.lower,108889201598590+c.upper)) = pointBounds40072 := by
 decide +kernel
def cuts40073 : List PrefixCut := [⟨53,261317324,261317479⟩,
⟨64,314276264,314276449⟩]
theorem checked40073 : checkPrefixCuts (2^48) 5256380417 10 Manual.Count131072.C040073.packed 64 cuts40073 = true := by
 decide +kernel
def pointBounds40073 : List (Nat × Nat × Nat) := [(5256488960,108889389164146,108889774683492)]
theorem point_links_checked40073 : (cuts40073.take 1).map (fun c => (5256380417-1+2*2^10*c.k,108889127846822+c.lower,108889513366013+c.upper)) = pointBounds40073 := by
 decide +kernel
def cuts40074 : List PrefixCut := [⟨64,317909674,317909860⟩]
theorem checked40074 : checkPrefixCuts (2^48) 5256511489 10 Manual.Count131072.C040074.packed 64 cuts40074 = true := by
 decide +kernel
def cuts40075 : List PrefixCut := [⟨6,28700897,28700915⟩,
⟨64,315706312,315706502⟩]
theorem checked40075 : checkPrefixCuts (2^48) 5256642561 10 Manual.Count131072.C040075.packed 64 cuts40075 = true := by
 decide +kernel
def pointBounds40075 : List (Nat × Nat × Nat) := [(5256654848,108889788733657,108890174253237)]
theorem point_links_checked40075 : (cuts40075.take 1).map (fun c => (5256642561-1+2*2^10*c.k,108889760032760+c.lower,108890145552322+c.upper)) = pointBounds40075 := by
 decide +kernel
def cuts40076 : List PrefixCut := [⟨23,110945116,110945179⟩,
⟨64,315323592,315323772⟩]
theorem checked40076 : checkPrefixCuts (2^48) 5256773633 10 Manual.Count131072.C040076.packed 64 cuts40076 = true := by
 decide +kernel
def pointBounds40076 : List (Nat × Nat × Nat) := [(5256820736,108890186684188,108890572204003)]
theorem point_links_checked40076 : (cuts40076.take 1).map (fun c => (5256773633-1+2*2^10*c.k,108890075739072+c.lower,108890461258824+c.upper)) = pointBounds40076 := by
 decide +kernel
def cuts40077 : List PrefixCut := [⟨40,195861855,195861975⟩,
⟨64,313495299,313495490⟩]
theorem checked40077 : checkPrefixCuts (2^48) 5256904705 10 Manual.Count131072.C040077.packed 64 cuts40077 = true := by
 decide +kernel
def pointBounds40077 : List (Nat × Nat × Nat) := [(5256986624,108890586924519,108890972444571)]
theorem point_links_checked40077 : (cuts40077.take 1).map (fun c => (5256904705-1+2*2^10*c.k,108890391062664+c.lower,108890776582596+c.upper)) = pointBounds40077 := by
 decide +kernel
def cuts40078 : List PrefixCut := [⟨57,279060460,279060625⟩,
⟨64,312523741,312523925⟩]
theorem checked40078 : checkPrefixCuts (2^48) 5257035777 10 Manual.Count131072.C040078.packed 64 cuts40078 = true := by
 decide +kernel
def pointBounds40078 : List (Nat × Nat × Nat) := [(5257152512,108890983618423,108891369138711)]
theorem point_links_checked40078 : (cuts40078.take 1).map (fun c => (5257035777-1+2*2^10*c.k,108890704557963+c.lower,108891090078086+c.upper)) = pointBounds40078 := by
 decide +kernel
def cuts40079 : List PrefixCut := [⟨64,320279323,320279508⟩]
theorem checked40079 : checkPrefixCuts (2^48) 5257166849 10 Manual.Count131072.C040079.packed 64 cuts40079 = true := by
 decide +kernel
def cuts40080 : List PrefixCut := [⟨10,48828239,48828269⟩,
⟨64,309028114,309028302⟩]
theorem checked40080 : checkPrefixCuts (2^48) 5257297921 10 Manual.Count131072.C040080.packed 64 cuts40080 = true := by
 decide +kernel
def pointBounds40080 : List (Nat × Nat × Nat) := [(5257318400,108891386189266,108891771709788)]
theorem point_links_checked40080 : (cuts40080.take 1).map (fun c => (5257297921-1+2*2^10*c.k,108891337361027+c.lower,108891722881519+c.upper)) = pointBounds40080 := by
 decide +kernel
def cuts40081 : List PrefixCut := [⟨27,133577866,133577945⟩,
⟨64,313892361,313892546⟩]
theorem checked40081 : checkPrefixCuts (2^48) 5257428993 10 Manual.Count131072.C040081.packed 64 cuts40081 = true := by
 decide +kernel
def pointBounds40081 : List (Nat × Nat × Nat) := [(5257484288,108891779967007,108892165487766)]
theorem point_links_checked40081 : (cuts40081.take 1).map (fun c => (5257428993-1+2*2^10*c.k,108891646389141+c.lower,108892031909821+c.upper)) = pointBounds40081 := by
 decide +kernel
def cuts40082 : List PrefixCut := [⟨44,215699414,215699543⟩,
⟨64,312117829,312118015⟩]
theorem checked40082 : checkPrefixCuts (2^48) 5257560065 10 Manual.Count131072.C040082.packed 64 cuts40082 = true := by
 decide +kernel
def pointBounds40082 : List (Nat × Nat × Nat) := [(5257650176,108892175980916,108892561501910)]
theorem point_links_checked40082 : (cuts40082.take 1).map (fun c => (5257560065-1+2*2^10*c.k,108891960281502+c.lower,108892345802367+c.upper)) = pointBounds40082 := by
 decide +kernel
def cuts40083 : List PrefixCut := [⟨61,300493075,300493252⟩,
⟨64,314358518,314358704⟩]
theorem checked40083 : checkPrefixCuts (2^48) 5257691137 10 Manual.Count131072.C040083.packed 64 cuts40083 = true := by
 decide +kernel
def pointBounds40083 : List (Nat × Nat × Nat) := [(5257816064,108892572892406,108892958413634)]
theorem point_links_checked40083 : (cuts40083.take 1).map (fun c => (5257691137-1+2*2^10*c.k,108892272399331+c.lower,108892657920382+c.upper)) = pointBounds40083 := by
 decide +kernel
def cuts40084 : List PrefixCut := [⟨64,315100184,315100371⟩]
theorem checked40084 : checkPrefixCuts (2^48) 5257822209 10 Manual.Count131072.C040084.packed 64 cuts40084 = true := by
 decide +kernel
def cuts40085 : List PrefixCut := [⟨14,70395927,70395967⟩,
⟨64,317019468,317019654⟩]
theorem checked40085 : checkPrefixCuts (2^48) 5257953281 10 Manual.Count131072.C040085.packed 64 cuts40085 = true := by
 decide +kernel
def pointBounds40085 : List (Nat × Nat × Nat) := [(5257981952,108892972253960,108893357775424)]
theorem point_links_checked40085 : (cuts40085.take 1).map (fun c => (5257953281-1+2*2^10*c.k,108892901858033+c.lower,108893287379457+c.upper)) = pointBounds40085 := by
 decide +kernel
def cuts40086 : List PrefixCut := [⟨31,149727630,149727718⟩,
⟨64,311016050,311016234⟩]
theorem checked40086 : checkPrefixCuts (2^48) 5258084353 10 Manual.Count131072.C040086.packed 64 cuts40086 = true := by
 decide +kernel
def pointBounds40086 : List (Nat × Nat × Nat) := [(5258147840,108893368605131,108893754126829)]
theorem point_links_checked40086 : (cuts40086.take 1).map (fun c => (5258084353-1+2*2^10*c.k,108893218877501+c.lower,108893604399111+c.upper)) = pointBounds40086 := by
 decide +kernel
def cuts40087 : List PrefixCut := [⟨48,230981921,230982058⟩,
⟨64,308545920,308546102⟩]
theorem checked40087 : checkPrefixCuts (2^48) 5258215425 10 Manual.Count131072.C040087.packed 64 cuts40087 = true := by
 decide +kernel
def pointBounds40087 : List (Nat × Nat × Nat) := [(5258313728,108893760875472,108894146397403)]
theorem point_links_checked40087 : (cuts40087.take 1).map (fun c => (5258215425-1+2*2^10*c.k,108893529893551+c.lower,108893915415345+c.upper)) = pointBounds40087 := by
 decide +kernel
def cuts40088 : List PrefixCut := [⟨64,308431191,308431377⟩]
theorem checked40088 : checkPrefixCuts (2^48) 5258346497 10 Manual.Count131072.C040088.packed 64 cuts40088 = true := by
 decide +kernel
def cuts40089 : List PrefixCut := [⟨1,4442809,4442812⟩,
⟨64,316024354,316024542⟩]
theorem checked40089 : checkPrefixCuts (2^48) 5258477569 10 Manual.Count131072.C040089.packed 64 cuts40089 = true := by
 decide +kernel
def pointBounds40089 : List (Nat × Nat × Nat) := [(5258479616,108894151313471,108894536835636)]
theorem point_links_checked40089 : (cuts40089.take 1).map (fun c => (5258477569-1+2*2^10*c.k,108894146870662+c.lower,108894532392824+c.upper)) = pointBounds40089 := by
 decide +kernel
def cuts40090 : List PrefixCut := [⟨18,90620041,90620095⟩,
⟨64,316605315,316605505⟩]
theorem checked40090 : checkPrefixCuts (2^48) 5258608641 10 Manual.Count131072.C040090.packed 64 cuts40090 = true := by
 decide +kernel
def pointBounds40090 : List (Nat × Nat × Nat) := [(5258645504,108894553515057,108894939037461)]
theorem point_links_checked40090 : (cuts40090.take 1).map (fun c => (5258608641-1+2*2^10*c.k,108894462895016+c.lower,108894848417366+c.upper)) = pointBounds40090 := by
 decide +kernel
def cuts40091 : List PrefixCut := [⟨35,171011719,171011820⟩,
⟨64,310335025,310335208⟩]
theorem checked40091 : checkPrefixCuts (2^48) 5258739713 10 Manual.Count131072.C040091.packed 64 cuts40091 = true := by
 decide +kernel
def pointBounds40091 : List (Nat × Nat × Nat) := [(5258811392,108894950512050,108895336034691)]
theorem point_links_checked40091 : (cuts40091.take 1).map (fun c => (5258739713-1+2*2^10*c.k,108894779500331+c.lower,108895165022871+c.upper)) = pointBounds40091 := by
 decide +kernel
def cuts40092 : List PrefixCut := [⟨52,255199024,255199177⟩,
⟨64,314662654,314662843⟩]
theorem checked40092 : checkPrefixCuts (2^48) 5258870785 10 Manual.Count131072.C040092.packed 64 cuts40092 = true := by
 decide +kernel
def pointBounds40092 : List (Nat × Nat × Nat) := [(5258977280,108895345034380,108895730557256)]
theorem point_links_checked40092 : (cuts40092.take 1).map (fun c => (5258870785-1+2*2^10*c.k,108895089835356+c.lower,108895475358079+c.upper)) = pointBounds40092 := by
 decide +kernel
def cuts40093 : List PrefixCut := [⟨64,316474539,316474723⟩]
theorem checked40093 : checkPrefixCuts (2^48) 5259001857 10 Manual.Count131072.C040093.packed 64 cuts40093 = true := by
 decide +kernel
def cuts40094 : List PrefixCut := [⟨5,23977455,23977470⟩,
⟨64,315396267,315396456⟩]
theorem checked40094 : checkPrefixCuts (2^48) 5259132929 10 Manual.Count131072.C040094.packed 64 cuts40094 = true := by
 decide +kernel
def pointBounds40094 : List (Nat × Nat × Nat) := [(5259143168,108895744950004,108896130473115)]
theorem point_links_checked40094 : (cuts40094.take 1).map (fun c => (5259132929-1+2*2^10*c.k,108895720972549+c.lower,108896106495645+c.upper)) = pointBounds40094 := by
 decide +kernel
def cuts40095 : List PrefixCut := [⟨22,105968804,105968865⟩,
⟨64,309875913,309876096⟩]
theorem checked40095 : checkPrefixCuts (2^48) 5259264001 10 Manual.Count131072.C040095.packed 64 cuts40095 = true := by
 decide +kernel
def pointBounds40095 : List (Nat × Nat × Nat) := [(5259309056,108896142337620,108896527860966)]
theorem point_links_checked40095 : (cuts40095.take 1).map (fun c => (5259264001-1+2*2^10*c.k,108896036368816+c.lower,108896421892101+c.upper)) = pointBounds40095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000002
