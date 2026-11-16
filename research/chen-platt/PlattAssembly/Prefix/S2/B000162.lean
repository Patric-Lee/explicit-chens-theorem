import PlattAssemblyKernel
import PlattCertificates.Count131072.C015184
import PlattCertificates.Count131072.C015185
import PlattCertificates.Count131072.C015186
import PlattCertificates.Count131072.C015187
import PlattCertificates.Count131072.C015188
import PlattCertificates.Count131072.C015189
import PlattCertificates.Count131072.C015190
import PlattCertificates.Count131072.C015191
import PlattCertificates.Count131072.C015192
import PlattCertificates.Count131072.C015193
import PlattCertificates.Count131072.C015194
import PlattCertificates.Count131072.C015195
import PlattCertificates.Count131072.C015196
import PlattCertificates.Count131072.C015197
import PlattCertificates.Count131072.C015198
import PlattCertificates.Count131072.C015199
import PlattCertificates.Count131072.C015200
import PlattCertificates.Count131072.C015201
import PlattCertificates.Count131072.C015202
import PlattCertificates.Count131072.C015203
import PlattCertificates.Count131072.C015204
import PlattCertificates.Count131072.C015205
import PlattCertificates.Count131072.C015206
import PlattCertificates.Count131072.C015207
import PlattCertificates.Count131072.C015208
import PlattCertificates.Count131072.C015209
import PlattCertificates.Count131072.C015210
import PlattCertificates.Count131072.C015211
import PlattCertificates.Count131072.C015212
import PlattCertificates.Count131072.C015213
import PlattCertificates.Count131072.C015214
import PlattCertificates.Count131072.C015215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15184 : List PrefixCut := [⟨14,96688617,96688679⟩,
⟨75,512935733,512936068⟩,
⟨128,871583699,871584277⟩]
theorem checked15184 : checkPrefixCuts (2^48) 1994129409 9 Manual.Count131072.C015184.packed 128 cuts15184 = true := by
 decide +kernel
def pointBounds15184 : List (Nat × Nat × Nat) := [(1994143744,96428875437795,96429253577999),(1994206208,96429291684911,96429669825388)]
theorem point_links_checked15184 : (cuts15184.take 2).map (fun c => (1994129409-1+2*2^9*c.k,96428778749178+c.lower,96429156889320+c.upper)) = pointBounds15184 := by
 decide +kernel
def cuts15185 : List PrefixCut := [⟨8,51940327,51940361⟩,
⟨69,466749820,466750131⟩,
⟨128,862634405,862634981⟩]
theorem checked15185 : checkPrefixCuts (2^48) 1994260481 9 Manual.Count131072.C015185.packed 128 cuts15185 = true := by
 decide +kernel
def pointBounds15185 : List (Nat × Nat × Nat) := [(1994268672,96429702273204,96430080413958),(1994331136,96430117082697,96430495223728)]
theorem point_links_checked15185 : (cuts15185.take 2).map (fun c => (1994260481-1+2*2^9*c.k,96429650332877+c.lower,96430028473597+c.upper)) = pointBounds15185 := by
 decide +kernel
def cuts15186 : List PrefixCut := [⟨2,12701983,12701991⟩,
⟨63,426074236,426074517⟩,
⟨124,842397284,842397839⟩,
⟨128,869351985,869352557⟩]
theorem checked15186 : checkPrefixCuts (2^48) 1994391553 9 Manual.Count131072.C015186.packed 128 cuts15186 = true := by
 decide +kernel
def pointBounds15186 : List (Nat × Nat × Nat) := [(1994393600,96430525669265,96430903810569),(1994456064,96430939041518,96431317183095),(1994518528,96431355364566,96431733506417)]
theorem point_links_checked15186 : (cuts15186.take 3).map (fun c => (1994391553-1+2*2^9*c.k,96430512967282+c.lower,96430891108578+c.upper)) = pointBounds15186 := by
 decide +kernel
def cuts15187 : List PrefixCut := [⟨57,390907591,390907849⟩,
⟨118,806075526,806076061⟩,
⟨128,872540692,872541272⟩]
theorem checked15187 : checkPrefixCuts (2^48) 1994522625 9 Manual.Count131072.C015187.packed 128 cuts15187 = true := by
 decide +kernel
def pointBounds15187 : List (Nat × Nat × Nat) := [(1994580992,96431773226858,96432151368984),(1994643456,96432188394793,96432566537196)]
theorem point_links_checked15187 : (cuts15187.take 2).map (fun c => (1994522625-1+2*2^9*c.k,96431382319267+c.lower,96431760461135+c.upper)) = pointBounds15187 := by
 decide +kernel
def cuts15188 : List PrefixCut := [⟨51,336977440,336977665⟩,
⟨112,750426150,750426651⟩,
⟨128,862323185,862323762⟩]
theorem checked15188 : checkPrefixCuts (2^48) 1994653697 9 Manual.Count131072.C015188.packed 128 cuts15188 = true := by
 decide +kernel
def pointBounds15188 : List (Nat × Nat × Nat) := [(1994705920,96432591837399,96432969980072),(1994768384,96433005286109,96433383429058)]
theorem point_links_checked15188 : (cuts15188.take 2).map (fun c => (1994653697-1+2*2^9*c.k,96432254859959+c.lower,96432633002407+c.upper)) = pointBounds15188 := by
 decide +kernel
def cuts15189 : List PrefixCut := [⟨45,307888380,307888582⟩,
⟨106,715667185,715667654⟩,
⟨128,866499775,866500346⟩]
theorem checked15189 : checkPrefixCuts (2^48) 1994784769 9 Manual.Count131072.C015189.packed 128 cuts15189 = true := by
 decide +kernel
def pointBounds15189 : List (Nat × Nat × Nat) := [(1994830848,96433425071524,96433803214751),(1994893312,96433832850329,96434210993823)]
theorem point_links_checked15189 : (cuts15189.take 2).map (fun c => (1994784769-1+2*2^9*c.k,96433117183144+c.lower,96433495326169+c.upper)) = pointBounds15189 := by
 decide +kernel
def cuts15190 : List PrefixCut := [⟨39,263988212,263988383⟩,
⟨100,674704373,674704809⟩,
⟨128,856566596,856567151⟩]
theorem checked15190 : checkPrefixCuts (2^48) 1994915841 9 Manual.Count131072.C015190.packed 128 cuts15190 = true := by
 decide +kernel
def pointBounds15190 : List (Nat × Nat × Nat) := [(1994955776,96434247671131,96434625814898),(1995018240,96434658387292,96435036531324)]
theorem point_links_checked15190 : (cuts15190.take 2).map (fun c => (1994915841-1+2*2^9*c.k,96433983682919+c.lower,96434361826515+c.upper)) = pointBounds15190 := by
 decide +kernel
def cuts15191 : List PrefixCut := [⟨33,215014545,215014689⟩,
⟨94,631489388,631489809⟩,
⟨128,867937488,867938070⟩]
theorem checked15191 : checkPrefixCuts (2^48) 1995046913 9 Manual.Count131072.C015191.packed 128 cuts15191 = true := by
 decide +kernel
def pointBounds15191 : List (Nat × Nat × Nat) := [(1995080704,96435055264060,96435433408355),(1995143168,96435471738903,96435849883475)]
theorem point_links_checked15191 : (cuts15191.take 2).map (fun c => (1995046913-1+2*2^9*c.k,96434840249515+c.lower,96435218393666+c.upper)) = pointBounds15191 := by
 decide +kernel
def cuts15192 : List PrefixCut := [⟨27,179872652,179872770⟩,
⟨88,588562430,588562815⟩,
⟨128,857159260,857159828⟩]
theorem checked15192 : checkPrefixCuts (2^48) 1995177985 9 Manual.Count131072.C015192.packed 128 cuts15192 = true := by
 decide +kernel
def pointBounds15192 : List (Nat × Nat × Nat) := [(1995205632,96435888059655,96436266204506),(1995268096,96436296749433,96436674894551)]
theorem point_links_checked15192 : (cuts15192.take 2).map (fun c => (1995177985-1+2*2^9*c.k,96435708187003+c.lower,96436086331736+c.upper)) = pointBounds15192 := by
 decide +kernel
def cuts15193 : List PrefixCut := [⟨21,143747842,143747936⟩,
⟨82,557913474,557913841⟩,
⟨128,862604615,862605184⟩]
theorem checked15193 : checkPrefixCuts (2^48) 1995309057 9 Manual.Count131072.C015193.packed 128 cuts15193 = true := by
 decide +kernel
def pointBounds15193 : List (Nat × Nat × Nat) := [(1995330560,96436709094105,96437087239500),(1995393024,96437123259737,96437501405405)]
theorem point_links_checked15193 : (cuts15193.take 2).map (fun c => (1995309057-1+2*2^9*c.k,96436565346263+c.lower,96436943491564+c.upper)) = pointBounds15193 := by
 decide +kernel
def cuts15194 : List PrefixCut := [⟨15,100997888,100997952⟩,
⟨76,514855445,514855782⟩,
⟨128,863817298,863817861⟩]
theorem checked15194 : checkPrefixCuts (2^48) 1995440129 9 Manual.Count131072.C015194.packed 128 cuts15194 = true := by
 decide +kernel
def pointBounds15194 : List (Nat × Nat × Nat) := [(1995455488,96437528948766,96437907094700),(1995517952,96437942806323,96438320952530)]
theorem point_links_checked15194 : (cuts15194.take 2).map (fun c => (1995440129-1+2*2^9*c.k,96437427950878+c.lower,96437806096748+c.upper)) = pointBounds15194 := by
 decide +kernel
def cuts15195 : List PrefixCut := [⟨9,58817623,58817661⟩,
⟨70,461788671,461788976⟩,
⟨128,847258148,847258712⟩]
theorem checked15195 : checkPrefixCuts (2^48) 1995571201 9 Manual.Count131072.C015195.packed 128 cuts15195 = true := by
 decide +kernel
def pointBounds15195 : List (Nat × Nat × Nat) := [(1995580416,96438350585799,96438728732270),(1995642880,96438753556847,96439131703585)]
theorem point_links_checked15195 : (cuts15195.take 2).map (fun c => (1995571201-1+2*2^9*c.k,96438291768176+c.lower,96438669914609+c.upper)) = pointBounds15195 := by
 decide +kernel
def cuts15196 : List PrefixCut := [⟨3,23130628,23130644⟩,
⟨64,436372244,436372531⟩,
⟨125,846639255,846639811⟩,
⟨128,866101584,866102152⟩]
theorem checked15196 : checkPrefixCuts (2^48) 1995702273 9 Manual.Count131072.C015196.packed 128 cuts15196 = true := by
 decide +kernel
def pointBounds15196 : List (Nat × Nat × Nat) := [(1995705344,96439162156952,96439540303965),(1995767808,96439575398568,96439953545852),(1995830272,96439985665579,96440363813132)]
theorem point_links_checked15196 : (cuts15196.take 3).map (fun c => (1995702273-1+2*2^9*c.k,96439139026324+c.lower,96439517173321+c.upper)) = pointBounds15196 := by
 decide +kernel
def cuts15197 : List PrefixCut := [⟨58,398407319,398407587⟩,
⟨119,811469190,811469737⟩,
⟨128,868583234,868583820⟩]
theorem checked15197 : checkPrefixCuts (2^48) 1995833345 9 Manual.Count131072.C015197.packed 128 cuts15197 = true := by
 decide +kernel
def pointBounds15197 : List (Nat × Nat × Nat) := [(1995892736,96440403535227,96440781683060),(1995955200,96440816597098,96441194745210)]
theorem point_links_checked15197 : (cuts15197.take 2).map (fun c => (1995833345-1+2*2^9*c.k,96440005127908+c.lower,96440383275473+c.upper)) = pointBounds15197 := by
 decide +kernel
def cuts15198 : List PrefixCut := [⟨52,345499272,345499502⟩,
⟨113,755432886,755433386⟩,
⟨128,858372586,858373152⟩]
theorem checked15198 : checkPrefixCuts (2^48) 1995964417 9 Manual.Count131072.C015198.packed 128 cuts15198 = true := by
 decide +kernel
def pointBounds15198 : List (Nat × Nat × Nat) := [(1996017664,96441219210414,96441597358795),(1996080128,96441629144028,96442007292679)]
theorem point_links_checked15198 : (cuts15198.take 2).map (fun c => (1995964417-1+2*2^9*c.k,96440873711142+c.lower,96441251859293+c.upper)) = pointBounds15198 := by
 decide +kernel
def cuts15199 : List PrefixCut := [⟨46,321928286,321928497⟩,
⟨107,727465047,727465526⟩,
⟨128,867764278,867764847⟩]
theorem checked15199 : checkPrefixCuts (2^48) 1996095489 9 Manual.Count131072.C015199.packed 128 cuts15199 = true := by
 decide +kernel
def pointBounds15199 : List (Nat × Nat × Nat) := [(1996142592,96442054012014,96442432160942),(1996205056,96442459548775,96442837697971)]
theorem point_links_checked15199 : (cuts15199.take 2).map (fun c => (1996095489-1+2*2^9*c.k,96441732083728+c.lower,96442110232445+c.upper)) = pointBounds15199 := by
 decide +kernel
def cuts15200 : List PrefixCut := [⟨40,278197017,278197200⟩,
⟨101,693014176,693014634⟩,
⟨128,878845831,878846411⟩]
theorem checked15200 : checkPrefixCuts (2^48) 1996226561 9 Manual.Count131072.C015200.packed 128 cuts15200 = true := by
 decide +kernel
def pointBounds15200 : List (Nat × Nat × Nat) := [(1996267520,96442878045023,96443256194492),(1996329984,96443292862182,96443671011926)]
theorem point_links_checked15200 : (cuts15200.take 2).map (fun c => (1996226561-1+2*2^9*c.k,96442599848006+c.lower,96442977997292+c.upper)) = pointBounds15200 := by
 decide +kernel
def cuts15201 : List PrefixCut := [⟨34,225165772,225165921⟩,
⟨95,625576098,625576512⟩,
⟨128,849462124,849462684⟩]
theorem checked15201 : checkPrefixCuts (2^48) 1996357633 9 Manual.Count131072.C015201.packed 128 cuts15201 = true := by
 decide +kernel
def pointBounds15201 : List (Nat × Nat × Nat) := [(1996392448,96443703859609,96444082009624),(1996454912,96444104269935,96444482420215)]
theorem point_links_checked15201 : (cuts15201.take 2).map (fun c => (1996357633-1+2*2^9*c.k,96443478693837+c.lower,96443856843703+c.upper)) = pointBounds15201 := by
 decide +kernel
def cuts15202 : List PrefixCut := [⟨28,189623413,189623536⟩,
⟨89,597198637,597199031⟩,
⟨128,849124773,849125333⟩]
theorem checked15202 : checkPrefixCuts (2^48) 1996488705 9 Manual.Count131072.C015202.packed 128 cuts15202 = true := by
 decide +kernel
def pointBounds15202 : List (Nat × Nat × Nat) := [(1996517376,96444517779374,96444895929923),(1996579840,96444925354598,96445303505418)]
theorem point_links_checked15202 : (cuts15202.take 2).map (fun c => (1996488705-1+2*2^9*c.k,96444328155961+c.lower,96444706306387+c.upper)) = pointBounds15202 := by
 decide +kernel
def cuts15203 : List PrefixCut := [⟨22,151125099,151125200⟩,
⟨83,558956827,558957198⟩,
⟨128,858513987,858514559⟩]
theorem checked15203 : checkPrefixCuts (2^48) 1996619777 9 Manual.Count131072.C015203.packed 128 cuts15203 = true := by
 decide +kernel
def pointBounds15203 : List (Nat × Nat × Nat) := [(1996642304,96445328405833,96445706556920),(1996704768,96445736237561,96446114388918)]
theorem point_links_checked15203 : (cuts15203.take 2).map (fun c => (1996619777-1+2*2^9*c.k,96445177280734+c.lower,96445555431720+c.upper)) = pointBounds15203 := by
 decide +kernel
def cuts15204 : List PrefixCut := [⟨16,105019571,105019643⟩,
⟨77,517336630,517336975⟩,
⟨128,861558598,861559171⟩]
theorem checked15204 : checkPrefixCuts (2^48) 1996750849 9 Manual.Count131072.C015204.packed 128 cuts15204 = true := by
 decide +kernel
def pointBounds15204 : List (Nat × Nat × Nat) := [(1996767232,96446140814292,96446518965922),(1996829696,96446553131351,96446931283254)]
theorem point_links_checked15204 : (cuts15204.take 2).map (fun c => (1996750849-1+2*2^9*c.k,96446035794721+c.lower,96446413946279+c.upper)) = pointBounds15204 := by
 decide +kernel
def cuts15205 : List PrefixCut := [⟨10,67941190,67941236⟩,
⟨71,469660848,469661159⟩,
⟨128,853467820,853468387⟩]
theorem checked15205 : checkPrefixCuts (2^48) 1996881921 9 Manual.Count131072.C015205.packed 128 cuts15205 = true := by
 decide +kernel
def pointBounds15205 : List (Nat × Nat × Nat) := [(1996892160,96446965294509,96447343446686),(1996954624,96447367014167,96447745166609)]
theorem point_links_checked15205 : (cuts15205.take 2).map (fun c => (1996881921-1+2*2^9*c.k,96446897353319+c.lower,96447275505450+c.upper)) = pointBounds15205 := by
 decide +kernel
def cuts15206 : List PrefixCut := [⟨4,24947761,24947777⟩,
⟨65,434535270,434535562⟩,
⟨126,843405266,843405828⟩,
⟨128,856512572,856513142⟩]
theorem checked15206 : checkPrefixCuts (2^48) 1997012993 9 Manual.Count131072.C015206.packed 128 cuts15206 = true := by
 decide +kernel
def pointBounds15206 : List (Nat × Nat × Nat) := [(1997017088,96447775768900,96448153921614),(1997079552,96448185356409,96448563509399),(1997142016,96448594226405,96448972379665)]
theorem point_links_checked15206 : (cuts15206.take 3).map (fun c => (1997012993-1+2*2^9*c.k,96447750821139+c.lower,96448128973837+c.upper)) = pointBounds15206 := by
 decide +kernel
def cuts15207 : List PrefixCut := [⟨59,401246451,401246720⟩,
⟨120,822351985,822352532⟩,
⟨128,877032729,877033310⟩]
theorem checked15207 : checkPrefixCuts (2^48) 1997144065 9 Manual.Count131072.C015207.packed 128 cuts15207 = true := by
 decide +kernel
def pointBounds15207 : List (Nat × Nat × Nat) := [(1997204480,96449008580162,96449386733699),(1997266944,96449429685696,96449807839511)]
theorem point_links_checked15207 : (cuts15207.take 2).map (fun c => (1997144065-1+2*2^9*c.k,96448607333711+c.lower,96448985486979+c.upper)) = pointBounds15207 := by
 decide +kernel
def cuts15208 : List PrefixCut := [⟨53,360915390,360915627⟩,
⟨114,774384703,774385217⟩,
⟨128,869788020,869788599⟩]
theorem checked15208 : checkPrefixCuts (2^48) 1997275137 9 Manual.Count131072.C015208.packed 128 cuts15208 = true := by
 decide +kernel
def pointBounds15208 : List (Nat × Nat × Nat) := [(1997329408,96449845281830,96450223435916),(1997391872,96450258751143,96450636905506)]
theorem point_links_checked15208 : (cuts15208.take 2).map (fun c => (1997275137-1+2*2^9*c.k,96449484366440+c.lower,96449862520289+c.upper)) = pointBounds15208 := by
 decide +kernel
def cuts15209 : List PrefixCut := [⟨47,321998897,321999112⟩,
⟨108,727269284,727269767⟩,
⟨128,863249062,863249633⟩]
theorem checked15209 : checkPrefixCuts (2^48) 1997406209 9 Manual.Count131072.C015209.packed 128 cuts15209 = true := by
 decide +kernel
def pointBounds15209 : List (Nat × Nat × Nat) := [(1997454336,96450676153357,96451054308000),(1997516800,96451081423744,96451459578655)]
theorem point_links_checked15209 : (cuts15209.take 2).map (fun c => (1997406209-1+2*2^9*c.k,96450354154460+c.lower,96450732308888+c.upper)) = pointBounds15209 := by
 decide +kernel
def cuts15210 : List PrefixCut := [⟨41,281818942,281819127⟩,
⟨102,698618237,698618694⟩,
⟨128,874746547,874747117⟩]
theorem checked15210 : checkPrefixCuts (2^48) 1997537281 9 Manual.Count131072.C015210.packed 128 cuts15210 = true := by
 decide +kernel
def pointBounds15210 : List (Nat × Nat × Nat) := [(1997579264,96451499222464,96451877377648),(1997641728,96451916021759,96452294177215)]
theorem point_links_checked15210 : (cuts15210.take 2).map (fun c => (1997537281-1+2*2^9*c.k,96451217403522+c.lower,96451595558521+c.upper)) = pointBounds15210 := by
 decide +kernel
def cuts15211 : List PrefixCut := [⟨35,236149124,236149285⟩,
⟨96,641509762,641510190⟩,
⟨128,853554675,853555244⟩]
theorem checked15211 : checkPrefixCuts (2^48) 1997668353 9 Manual.Count131072.C015211.packed 128 cuts15211 = true := by
 decide +kernel
def pointBounds15211 : List (Nat × Nat × Nat) := [(1997704192,96452328299193,96452706454923),(1997766656,96452733659831,96453111815828)]
theorem point_links_checked15211 : (cuts15211.take 2).map (fun c => (1997668353-1+2*2^9*c.k,96452092150069+c.lower,96452470305638+c.upper)) = pointBounds15211 := by
 decide +kernel
def cuts15212 : List PrefixCut := [⟨29,199502240,199502372⟩,
⟨90,610613857,610614265⟩,
⟨128,867023824,867024399⟩]
theorem checked15212 : checkPrefixCuts (2^48) 1997799425 9 Manual.Count131072.C015212.packed 128 cuts15212 = true := by
 decide +kernel
def pointBounds15212 : List (Nat × Nat × Nat) := [(1997829120,96453145206984,96453523363254),(1997891584,96453556318601,96453934475147)]
theorem point_links_checked15212 : (cuts15212.take 2).map (fun c => (1997799425-1+2*2^9*c.k,96452945704744+c.lower,96453323860882+c.upper)) = pointBounds15212 := by
 decide +kernel
def cuts15213 : List PrefixCut := [⟨23,155815904,155816006⟩,
⟨84,567887992,567888359⟩,
⟨128,863022316,863022879⟩]
theorem checked15213 : checkPrefixCuts (2^48) 1997930497 9 Manual.Count131072.C015213.packed 128 cuts15213 = true := by
 decide +kernel
def pointBounds15213 : List (Nat × Nat × Nat) := [(1997954048,96453968544472,96454346701287),(1998016512,96454380616560,96454758773640)]
theorem point_links_checked15213 : (cuts15213.take 2).map (fun c => (1997930497-1+2*2^9*c.k,96453812728568+c.lower,96454190885281+c.upper)) = pointBounds15213 := by
 decide +kernel
def cuts15214 : List PrefixCut := [⟨17,111289954,111290030⟩,
⟨78,519110178,519110528⟩,
⟨128,858880263,858880836⟩]
theorem checked15214 : checkPrefixCuts (2^48) 1998061569 9 Manual.Count131072.C015214.packed 128 cuts15214 = true := by
 decide +kernel
def pointBounds15214 : List (Nat × Nat × Nat) := [(1998078976,96454787040838,96455165198190),(1998141440,96455194861062,96455573018688)]
theorem point_links_checked15214 : (cuts15214.take 2).map (fun c => (1998061569-1+2*2^9*c.k,96454675750884+c.lower,96455053908160+c.upper)) = pointBounds15214 := by
 decide +kernel
def cuts15215 : List PrefixCut := [⟨11,73390314,73390362⟩,
⟨72,482312005,482312323⟩,
⟨128,861641224,861641793⟩]
theorem checked15215 : checkPrefixCuts (2^48) 1998192641 9 Manual.Count131072.C015215.packed 128 cuts15215 = true := by
 decide +kernel
def pointBounds15215 : List (Nat × Nat × Nat) := [(1998203904,96455608021461,96455986179358),(1998266368,96456016943152,96456395101319)]
theorem point_links_checked15215 : (cuts15215.take 2).map (fun c => (1998192641-1+2*2^9*c.k,96455534631147+c.lower,96455912788996+c.upper)) = pointBounds15215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000162
