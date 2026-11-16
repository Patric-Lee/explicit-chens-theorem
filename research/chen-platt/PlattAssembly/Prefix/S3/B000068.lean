import PlattAssemblyKernel
import PlattCertificates.Count131072.C022176
import PlattCertificates.Count131072.C022177
import PlattCertificates.Count131072.C022178
import PlattCertificates.Count131072.C022179
import PlattCertificates.Count131072.C022180
import PlattCertificates.Count131072.C022181
import PlattCertificates.Count131072.C022182
import PlattCertificates.Count131072.C022183
import PlattCertificates.Count131072.C022184
import PlattCertificates.Count131072.C022185
import PlattCertificates.Count131072.C022186
import PlattCertificates.Count131072.C022187
import PlattCertificates.Count131072.C022188
import PlattCertificates.Count131072.C022189
import PlattCertificates.Count131072.C022190
import PlattCertificates.Count131072.C022191
import PlattCertificates.Count131072.C022192
import PlattCertificates.Count131072.C022193
import PlattCertificates.Count131072.C022194
import PlattCertificates.Count131072.C022195
import PlattCertificates.Count131072.C022196
import PlattCertificates.Count131072.C022197
import PlattCertificates.Count131072.C022198
import PlattCertificates.Count131072.C022199
import PlattCertificates.Count131072.C022200
import PlattCertificates.Count131072.C022201
import PlattCertificates.Count131072.C022202
import PlattCertificates.Count131072.C022203
import PlattCertificates.Count131072.C022204
import PlattCertificates.Count131072.C022205
import PlattCertificates.Count131072.C022206
import PlattCertificates.Count131072.C022207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22176 : List PrefixCut := [⟨34,155020949,155021033⟩,
⟨123,557699164,557699483⟩,
⟨128,578200212,578200544⟩]
theorem checked22176 : checkPrefixCuts (2^48) 2910584833 9 Manual.Count131072.C022176.packed 128 cuts22176 = true := by
 decide +kernel
def pointBounds22176 : List (Nat × Nat × Nat) := [(2910619648,101356238834271,101356619977429),(2910710784,101356641512486,101357022655879)]
theorem point_links_checked22176 : (cuts22176.take 2).map (fun c => (2910584833-1+2*2^9*c.k,101356083813322+c.lower,101356464956396+c.upper)) = pointBounds22176 := by
 decide +kernel
def cuts22177 : List PrefixCut := [⟨84,385162240,385162460⟩,
⟨128,581171885,581172217⟩]
theorem checked22177 : checkPrefixCuts (2^48) 2910715905 9 Manual.Count131072.C022177.packed 128 cuts22177 = true := by
 decide +kernel
def pointBounds22177 : List (Nat × Nat × Nat) := [(2910801920,101357047175774,101357428319400)]
theorem point_links_checked22177 : (cuts22177.take 1).map (fun c => (2910715905-1+2*2^9*c.k,101356662013534+c.lower,101357043156940+c.upper)) = pointBounds22177 := by
 decide +kernel
def cuts22178 : List PrefixCut := [⟨45,203839109,203839223⟩,
⟨128,583273017,583273343⟩]
theorem checked22178 : checkPrefixCuts (2^48) 2910846977 9 Manual.Count131072.C022178.packed 128 cuts22178 = true := by
 decide +kernel
def pointBounds22178 : List (Nat × Nat × Nat) := [(2910893056,101357447024528,101357828168380)]
theorem point_links_checked22178 : (cuts22178.take 1).map (fun c => (2910846977-1+2*2^9*c.k,101357243185419+c.lower,101357624329157+c.upper)) = pointBounds22178 := by
 decide +kernel
def cuts22179 : List PrefixCut := [⟨6,26204121,26204136⟩,
⟨95,427478217,427478463⟩,
⟨128,579475638,579475973⟩]
theorem checked22179 : checkPrefixCuts (2^48) 2910978049 9 Manual.Count131072.C022179.packed 128 cuts22179 = true := by
 decide +kernel
def pointBounds22179 : List (Nat × Nat × Nat) := [(2910984192,101357852662557,101358233806636),(2911075328,101358253936653,101358635080963)]
theorem point_links_checked22179 : (cuts22179.take 2).map (fun c => (2910978049-1+2*2^9*c.k,101357826458436+c.lower,101358207602500+c.upper)) = pointBounds22179 := by
 decide +kernel
def cuts22180 : List PrefixCut := [⟨56,254001892,254002034⟩,
⟨128,582253532,582253862⟩]
theorem checked22180 : checkPrefixCuts (2^48) 2911109121 9 Manual.Count131072.C022180.packed 128 cuts22180 = true := by
 decide +kernel
def pointBounds22180 : List (Nat × Nat × Nat) := [(2911166464,101358659935966,101359041080507)]
theorem point_links_checked22180 : (cuts22180.take 1).map (fun c => (2911109121-1+2*2^9*c.k,101358405934074+c.lower,101358787078473+c.upper)) = pointBounds22180 := by
 decide +kernel
def cuts22181 : List PrefixCut := [⟨17,79765348,79765395⟩,
⟨106,472300193,472300463⟩,
⟨128,571785541,571785870⟩]
theorem checked22181 : checkPrefixCuts (2^48) 2911240193 9 Manual.Count131072.C022181.packed 128 cuts22181 = true := by
 decide +kernel
def pointBounds22181 : List (Nat × Nat × Nat) := [(2911257600,101359067952954,101359449097730),(2911348736,101359460487799,101359841632798)]
theorem point_links_checked22181 : (cuts22181.take 2).map (fun c => (2911240193-1+2*2^9*c.k,101358988187606+c.lower,101359369332335+c.upper)) = pointBounds22181 := by
 decide +kernel
def cuts22182 : List PrefixCut := [⟨67,302511902,302512079⟩,
⟨128,578720644,578720979⟩]
theorem checked22182 : checkPrefixCuts (2^48) 2911371265 9 Manual.Count131072.C022182.packed 128 cuts22182 = true := by
 decide +kernel
def pointBounds22182 : List (Nat × Nat × Nat) := [(2911439872,101359862485049,101360243630284)]
theorem point_links_checked22182 : (cuts22182.take 1).map (fun c => (2911371265-1+2*2^9*c.k,101359559973147+c.lower,101359941118205+c.upper)) = pointBounds22182 := by
 decide +kernel
def cuts22183 : List PrefixCut := [⟨28,128482914,128482987⟩,
⟨117,529391588,529391886⟩,
⟨128,577824606,577824932⟩]
theorem checked22183 : checkPrefixCuts (2^48) 2911502337 9 Manual.Count131072.C022183.packed 128 cuts22183 = true := by
 decide +kernel
def pointBounds22183 : List (Nat × Nat × Nat) := [(2911531008,101360267176705,101360648322171),(2911622144,101360668085379,101361049231070)]
theorem point_links_checked22183 : (cuts22183.take 2).map (fun c => (2911502337-1+2*2^9*c.k,101360138693791+c.lower,101360519839184+c.upper)) = pointBounds22183 := by
 decide +kernel
def cuts22184 : List PrefixCut := [⟨78,351979662,351979862⟩,
⟨128,578765133,578765466⟩]
theorem checked22184 : checkPrefixCuts (2^48) 2911633409 9 Manual.Count131072.C022184.packed 128 cuts22184 = true := by
 decide +kernel
def pointBounds22184 : List (Nat × Nat × Nat) := [(2911713280,101361068498059,101361449643978)]
theorem point_links_checked22184 : (cuts22184.take 1).map (fun c => (2911633409-1+2*2^9*c.k,101360716518397+c.lower,101361097664116+c.upper)) = pointBounds22184 := by
 decide +kernel
def cuts22185 : List PrefixCut := [⟨39,177191522,177191626⟩,
⟨128,581832528,581832858⟩]
theorem checked22185 : checkPrefixCuts (2^48) 2911764481 9 Manual.Count131072.C022185.packed 128 cuts22185 = true := by
 decide +kernel
def pointBounds22185 : List (Nat × Nat × Nat) := [(2911804416,101361472475052,101361853621208),(2911895552,101361877116058,101362258262440)]
theorem point_links_checked22185 : (cuts22185.take 2).map (fun c => (2911764481-1+2*2^9*c.k,101361295283530+c.lower,101361676429582+c.upper)) = pointBounds22185 := by
 decide +kernel
def cuts22186 : List PrefixCut := [⟨89,405498295,405498527⟩,
⟨128,579969786,579970119⟩]
theorem checked22186 : checkPrefixCuts (2^48) 2911895553 9 Manual.Count131072.C022186.packed 128 cuts22186 = true := by
 decide +kernel
def pointBounds22186 : List (Nat × Nat × Nat) := [(2911986688,101362282614353,101362663760967)]
theorem point_links_checked22186 : (cuts22186.take 1).map (fun c => (2911895553-1+2*2^9*c.k,101361877116058+c.lower,101362258262440+c.upper)) = pointBounds22186 := by
 decide +kernel
def cuts22187 : List PrefixCut := [⟨50,226664454,226664579⟩,
⟨128,578493841,578494170⟩]
theorem checked22187 : checkPrefixCuts (2^48) 2912026625 9 Manual.Count131072.C022187.packed 128 cuts22187 = true := by
 decide +kernel
def pointBounds22187 : List (Nat × Nat × Nat) := [(2912077824,101362683750298,101363064897138)]
theorem point_links_checked22187 : (cuts22187.take 1).map (fun c => (2912026625-1+2*2^9*c.k,101362457085844+c.lower,101362838232559+c.upper)) = pointBounds22187 := by
 decide +kernel
def cuts22188 : List PrefixCut := [⟨11,50647172,50647199⟩,
⟨100,462679846,462680109⟩,
⟨128,590452770,590453102⟩]
theorem checked22188 : checkPrefixCuts (2^48) 2912157697 9 Manual.Count131072.C022188.packed 128 cuts22188 = true := by
 decide +kernel
def pointBounds22188 : List (Nat × Nat × Nat) := [(2912168960,101363086226857,101363467373928),(2912260096,101363498259531,101363879406838)]
theorem point_links_checked22188 : (cuts22188.take 2).map (fun c => (2912157697-1+2*2^9*c.k,101363035579685+c.lower,101363416726729+c.upper)) = pointBounds22188 := by
 decide +kernel
def cuts22189 : List PrefixCut := [⟨61,276418179,276418341⟩,
⟨128,581437834,581438165⟩]
theorem checked22189 : checkPrefixCuts (2^48) 2912288769 9 Manual.Count131072.C022189.packed 128 cuts22189 = true := by
 decide +kernel
def pointBounds22189 : List (Nat × Nat × Nat) := [(2912351232,101363902450634,101364283598172)]
theorem point_links_checked22189 : (cuts22189.take 1).map (fun c => (2912288769-1+2*2^9*c.k,101363626032455+c.lower,101364007179831+c.upper)) = pointBounds22189 := by
 decide +kernel
def cuts22190 : List PrefixCut := [⟨22,99545408,99545467⟩,
⟨111,507480335,507480630⟩,
⟨128,583731145,583731482⟩]
theorem checked22190 : checkPrefixCuts (2^48) 2912419841 9 Manual.Count131072.C022190.packed 128 cuts22190 = true := by
 decide +kernel
def pointBounds22190 : List (Nat × Nat × Nat) := [(2912442368,101364307015697,101364688163463),(2912533504,101364714950624,101365096098626)]
theorem point_links_checked22190 : (cuts22190.take 2).map (fun c => (2912419841-1+2*2^9*c.k,101364207470289+c.lower,101364588617996+c.upper)) = pointBounds22190 := by
 decide +kernel
def cuts22191 : List PrefixCut := [⟨72,332637688,332637873⟩,
⟨128,584478005,584478333⟩]
theorem checked22191 : checkPrefixCuts (2^48) 2912550913 9 Manual.Count131072.C022191.packed 128 cuts22191 = true := by
 decide +kernel
def pointBounds22191 : List (Nat × Nat × Nat) := [(2912624640,101365123839122,101365504987351)]
theorem point_links_checked22191 : (cuts22191.take 1).map (fun c => (2912550913-1+2*2^9*c.k,101364791201434+c.lower,101365172349478+c.upper)) = pointBounds22191 := by
 decide +kernel
def cuts22192 : List PrefixCut := [⟨33,150560655,150560742⟩,
⟨122,553528887,553529204⟩,
⟨128,581455954,581456287⟩]
theorem checked22192 : checkPrefixCuts (2^48) 2912681985 9 Manual.Count131072.C022192.packed 128 cuts22192 = true := by
 decide +kernel
def pointBounds22192 : List (Nat × Nat × Nat) := [(2912715776,101365526240094,101365907388553),(2912806912,101365929208326,101366310357015)]
theorem point_links_checked22192 : (cuts22192.take 2).map (fun c => (2912681985-1+2*2^9*c.k,101365375679439+c.lower,101365756827811+c.upper)) = pointBounds22192 := by
 decide +kernel
def cuts22193 : List PrefixCut := [⟨83,377347764,377347982⟩,
⟨128,578434312,578434638⟩]
theorem checked22193 : checkPrefixCuts (2^48) 2912813057 9 Manual.Count131072.C022193.packed 128 cuts22193 = true := by
 decide +kernel
def pointBounds22193 : List (Nat × Nat × Nat) := [(2912898048,101366334483157,101366715632080)]
theorem point_links_checked22193 : (cuts22193.take 1).map (fun c => (2912813057-1+2*2^9*c.k,101365957135393+c.lower,101366338284098+c.upper)) = pointBounds22193 := by
 decide +kernel
def cuts22194 : List PrefixCut := [⟨44,199730622,199730739⟩,
⟨128,584399064,584399394⟩]
theorem checked22194 : checkPrefixCuts (2^48) 2912944129 9 Manual.Count131072.C022194.packed 128 cuts22194 = true := by
 decide +kernel
def pointBounds22194 : List (Nat × Nat × Nat) := [(2912989184,101366735300327,101367116449475)]
theorem point_links_checked22194 : (cuts22194.take 1).map (fun c => (2912944129-1+2*2^9*c.k,101366535569705+c.lower,101366916718736+c.upper)) = pointBounds22194 := by
 decide +kernel
def cuts22195 : List PrefixCut := [⟨5,23383147,23383161⟩,
⟨94,421083327,421083565⟩,
⟨128,575869967,575870295⟩]
theorem checked22195 : checkPrefixCuts (2^48) 2913075201 9 Manual.Count131072.C022195.packed 128 cuts22195 = true := by
 decide +kernel
def pointBounds22195 : List (Nat × Nat × Nat) := [(2913080320,101367143351916,101367524501291),(2913171456,101367541052096,101367922201695)]
theorem point_links_checked22195 : (cuts22195.take 2).map (fun c => (2913075201-1+2*2^9*c.k,101367119968769+c.lower,101367501118130+c.upper)) = pointBounds22195 := by
 decide +kernel
def cuts22196 : List PrefixCut := [⟨55,254881905,254882048⟩,
⟨128,583960130,583960462⟩]
theorem checked22196 : checkPrefixCuts (2^48) 2913206273 9 Manual.Count131072.C022196.packed 128 cuts22196 = true := by
 decide +kernel
def pointBounds22196 : List (Nat × Nat × Nat) := [(2913262592,101367950720641,101368331870473)]
theorem point_links_checked22196 : (cuts22196.take 1).map (fun c => (2913206273-1+2*2^9*c.k,101367695838736+c.lower,101368076988425+c.upper)) = pointBounds22196 := by
 decide +kernel
def cuts22197 : List PrefixCut := [⟨16,72365154,72365196⟩,
⟨105,474762137,474762413⟩,
⟨128,577653919,577654255⟩]
theorem checked22197 : checkPrefixCuts (2^48) 2913337345 9 Manual.Count131072.C022197.packed 128 cuts22197 = true := by
 decide +kernel
def pointBounds22197 : List (Nat × Nat × Nat) := [(2913353728,101368352164020,101368733314083),(2913444864,101368754561003,101369135711300)]
theorem point_links_checked22197 : (cuts22197.take 2).map (fun c => (2913337345-1+2*2^9*c.k,101368279798866+c.lower,101368660948887+c.upper)) = pointBounds22197 := by
 decide +kernel
def cuts22198 : List PrefixCut := [⟨66,294951838,294952005⟩,
⟨128,575405831,575406164⟩]
theorem checked22198 : checkPrefixCuts (2^48) 2913468417 9 Manual.Count131072.C022198.packed 128 cuts22198 = true := by
 decide +kernel
def pointBounds22198 : List (Nat × Nat × Nat) := [(2913536000,101369152404623,101369533555147)]
theorem point_links_checked22198 : (cuts22198.take 1).map (fun c => (2913468417-1+2*2^9*c.k,101368857452785+c.lower,101369238603142+c.upper)) = pointBounds22198 := by
 decide +kernel
def cuts22199 : List PrefixCut := [⟨27,122014396,122014466⟩,
⟨116,523987157,523987457⟩,
⟨128,578857729,578858060⟩]
theorem checked22199 : checkPrefixCuts (2^48) 2913599489 9 Manual.Count131072.C022199.packed 128 cuts22199 = true := by
 decide +kernel
def pointBounds22199 : List (Nat × Nat × Nat) := [(2913627136,101369554873012,101369936023772),(2913718272,101369956845773,101370337996763)]
theorem point_links_checked22199 : (cuts22199.take 2).map (fun c => (2913599489-1+2*2^9*c.k,101369432858616+c.lower,101369814009306+c.upper)) = pointBounds22199 := by
 decide +kernel
def cuts22200 : List PrefixCut := [⟨77,352982294,352982494⟩,
⟨128,582212797,582213130⟩]
theorem checked22200 : checkPrefixCuts (2^48) 2913730561 9 Manual.Count131072.C022200.packed 128 cuts22200 = true := by
 decide +kernel
def pointBounds22200 : List (Nat × Nat × Nat) := [(2913809408,101370364698639,101370745849860)]
theorem point_links_checked22200 : (cuts22200.take 1).map (fun c => (2913730561-1+2*2^9*c.k,101370011716345+c.lower,101370392867366+c.upper)) = pointBounds22200 := by
 decide +kernel
def cuts22201 : List PrefixCut := [⟨38,170012357,170012455⟩,
⟨127,571464387,571464713⟩,
⟨128,576197505,576197834⟩]
theorem checked22201 : checkPrefixCuts (2^48) 2913861633 9 Manual.Count131072.C022201.packed 128 cuts22201 = true := by
 decide +kernel
def pointBounds22201 : List (Nat × Nat × Nat) := [(2913900544,101370763941499,101371145092951),(2913991680,101371165393529,101371546545209)]
theorem point_links_checked22201 : (cuts22201.take 2).map (fun c => (2913861633-1+2*2^9*c.k,101370593929142+c.lower,101370975080496+c.upper)) = pointBounds22201 := by
 decide +kernel
def cuts22202 : List PrefixCut := [⟨88,398831464,398831689⟩,
⟨128,577330843,577331167⟩]
theorem checked22202 : checkPrefixCuts (2^48) 2913992705 9 Manual.Count131072.C022202.packed 128 cuts22202 = true := by
 decide +kernel
def pointBounds22202 : List (Nat × Nat × Nat) := [(2914082816,101371568958111,101371950110019)]
theorem point_links_checked22202 : (cuts22202.take 1).map (fun c => (2913992705-1+2*2^9*c.k,101371170126647+c.lower,101371551278330+c.upper)) = pointBounds22202 := by
 decide +kernel
def cuts22203 : List PrefixCut := [⟨49,225149118,225149255⟩,
⟨128,583196716,583197065⟩]
theorem checked22203 : checkPrefixCuts (2^48) 2914123777 9 Manual.Count131072.C022203.packed 128 cuts22203 = true := by
 decide +kernel
def pointBounds22203 : List (Nat × Nat × Nat) := [(2914173952,101371972606608,101372353758752)]
theorem point_links_checked22203 : (cuts22203.take 1).map (fun c => (2914123777-1+2*2^9*c.k,101371747457490+c.lower,101372128609497+c.upper)) = pointBounds22203 := by
 decide +kernel
def cuts22204 : List PrefixCut := [⟨10,46167810,46167835⟩,
⟨99,452881821,452882079⟩,
⟨128,584715840,584716172⟩]
theorem checked22204 : checkPrefixCuts (2^48) 2914254849 9 Manual.Count131072.C022204.packed 128 cuts22204 = true := by
 decide +kernel
def pointBounds22204 : List (Nat × Nat × Nat) := [(2914265088,101372376822016,101372757974397),(2914356224,101372783536027,101373164688641)]
theorem point_links_checked22204 : (cuts22204.take 2).map (fun c => (2914254849-1+2*2^9*c.k,101372330654206+c.lower,101372711806562+c.upper)) = pointBounds22204 := by
 decide +kernel
def cuts22205 : List PrefixCut := [⟨60,276122741,276122893⟩,
⟨128,582854481,582854811⟩]
theorem checked22205 : checkPrefixCuts (2^48) 2914385921 9 Manual.Count131072.C022205.packed 128 cuts22205 = true := by
 decide +kernel
def pointBounds22205 : List (Nat × Nat × Nat) := [(2914447360,101373191492787,101373572645627)]
theorem point_links_checked22205 : (cuts22205.take 1).map (fun c => (2914385921-1+2*2^9*c.k,101372915370046+c.lower,101373296522734+c.upper)) = pointBounds22205 := by
 decide +kernel
def cuts22206 : List PrefixCut := [⟨21,91071636,91071690⟩,
⟨110,496298754,496299044⟩,
⟨128,582055424,582055760⟩]
theorem checked22206 : checkPrefixCuts (2^48) 2914516993 9 Manual.Count131072.C022206.packed 128 cuts22206 = true := by
 decide +kernel
def pointBounds22206 : List (Nat × Nat × Nat) := [(2914538496,101373589296163,101373970449235),(2914629632,101373994523281,101374375676589)]
theorem point_links_checked22206 : (cuts22206.take 2).map (fun c => (2914516993-1+2*2^9*c.k,101373498224527+c.lower,101373879377545+c.upper)) = pointBounds22206 := by
 decide +kernel
def cuts22207 : List PrefixCut := [⟨71,319168155,319168337⟩,
⟨128,578166619,578166951⟩]
theorem checked22207 : checkPrefixCuts (2^48) 2914648065 9 Manual.Count131072.C022207.packed 128 cuts22207 = true := by
 decide +kernel
def pointBounds22207 : List (Nat × Nat × Nat) := [(2914720768,101374399448106,101374780601642)]
theorem point_links_checked22207 : (cuts22207.take 1).map (fun c => (2914648065-1+2*2^9*c.k,101374080279951+c.lower,101374461433305+c.upper)) = pointBounds22207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000068
