import PlattAssemblyKernel
import PlattCertificates.Count131072.C028160
import PlattCertificates.Count131072.C028161
import PlattCertificates.Count131072.C028162
import PlattCertificates.Count131072.C028163
import PlattCertificates.Count131072.C028164
import PlattCertificates.Count131072.C028165
import PlattCertificates.Count131072.C028166
import PlattCertificates.Count131072.C028167
import PlattCertificates.Count131072.C028168
import PlattCertificates.Count131072.C028169
import PlattCertificates.Count131072.C028170
import PlattCertificates.Count131072.C028171
import PlattCertificates.Count131072.C028172
import PlattCertificates.Count131072.C028173
import PlattCertificates.Count131072.C028174
import PlattCertificates.Count131072.C028175
import PlattCertificates.Count131072.C028176
import PlattCertificates.Count131072.C028177
import PlattCertificates.Count131072.C028178
import PlattCertificates.Count131072.C028179
import PlattCertificates.Count131072.C028180
import PlattCertificates.Count131072.C028181
import PlattCertificates.Count131072.C028182
import PlattCertificates.Count131072.C028183
import PlattCertificates.Count131072.C028184
import PlattCertificates.Count131072.C028185
import PlattCertificates.Count131072.C028186
import PlattCertificates.Count131072.C028187
import PlattCertificates.Count131072.C028188
import PlattCertificates.Count131072.C028189
import PlattCertificates.Count131072.C028190
import PlattCertificates.Count131072.C028191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28160 : List PrefixCut := [⟨99,353160500,353160700⟩,
⟨128,456608184,456608446⟩]
theorem checked28160 : checkPrefixCuts (2^48) 3694919681 9 Manual.Count131072.C028160.packed 128 cuts28160 = true := by
 decide +kernel
def pointBounds28160 : List (Nat × Nat × Nat) := [(3695021056,104421631578855,104422014448279)]
theorem point_links_checked28160 : (cuts28160.take 1).map (fun c => (3694919681-1+2*2^9*c.k,104421278418355+c.lower,104421661287579+c.upper)) = pointBounds28160 := by
 decide +kernel
def cuts28161 : List PrefixCut := [⟨84,300054560,300054725⟩,
⟨128,456439692,456439942⟩]
theorem checked28161 : checkPrefixCuts (2^48) 3695050753 9 Manual.Count131072.C028161.packed 128 cuts28161 = true := by
 decide +kernel
def pointBounds28161 : List (Nat × Nat × Nat) := [(3695136768,104422035081099,104422417950750)]
theorem point_links_checked28161 : (cuts28161.take 1).map (fun c => (3695050753-1+2*2^9*c.k,104421735026539+c.lower,104422117896025+c.upper)) = pointBounds28161 := by
 decide +kernel
def cuts28162 : List PrefixCut := [⟨69,238116040,238116174⟩,
⟨128,450024910,450025161⟩]
theorem checked28162 : checkPrefixCuts (2^48) 3695181825 9 Manual.Count131072.C028162.packed 128 cuts28162 = true := by
 decide +kernel
def pointBounds28162 : List (Nat × Nat × Nat) := [(3695252480,104422429582271,104422812452141)]
theorem point_links_checked28162 : (cuts28162.take 1).map (fun c => (3695181825-1+2*2^9*c.k,104422191466231+c.lower,104422574335967+c.upper)) = pointBounds28162 := by
 decide +kernel
def cuts28163 : List PrefixCut := [⟨54,198575753,198575863⟩,
⟨128,458235427,458235685⟩]
theorem checked28163 : checkPrefixCuts (2^48) 3695312897 9 Manual.Count131072.C028163.packed 128 cuts28163 = true := by
 decide +kernel
def pointBounds28163 : List (Nat × Nat × Nat) := [(3695368192,104422840066894,104423222936991)]
theorem point_links_checked28163 : (cuts28163.take 1).map (fun c => (3695312897-1+2*2^9*c.k,104422641491141+c.lower,104423024361128+c.upper)) = pointBounds28163 := by
 decide +kernel
def cuts28164 : List PrefixCut := [⟨39,136340148,136340222⟩,
⟨128,453115867,453116119⟩]
theorem checked28164 : checkPrefixCuts (2^48) 3695443969 9 Manual.Count131072.C028164.packed 128 cuts28164 = true := by
 decide +kernel
def pointBounds28164 : List (Nat × Nat × Nat) := [(3695483904,104423236066716,104423618937035)]
theorem point_links_checked28164 : (cuts28164.take 1).map (fun c => (3695443969-1+2*2^9*c.k,104423099726568+c.lower,104423482596813+c.upper)) = pointBounds28164 := by
 decide +kernel
def cuts28165 : List PrefixCut := [⟨24,82867666,82867713⟩,
⟨128,450434051,450434301⟩]
theorem checked28165 : checkPrefixCuts (2^48) 3695575041 9 Manual.Count131072.C028165.packed 128 cuts28165 = true := by
 decide +kernel
def pointBounds28165 : List (Nat × Nat × Nat) := [(3695599616,104423635710101,104424018580645)]
theorem point_links_checked28165 : (cuts28165.take 1).map (fun c => (3695575041-1+2*2^9*c.k,104423552842435+c.lower,104423935712932+c.upper)) = pointBounds28165 := by
 decide +kernel
def cuts28166 : List PrefixCut := [⟨9,32064450,32064468⟩,
⟨122,429169527,429169772⟩,
⟨128,450798982,450799239⟩]
theorem checked28166 : checkPrefixCuts (2^48) 3695706113 9 Manual.Count131072.C028166.packed 128 cuts28166 = true := by
 decide +kernel
def pointBounds28166 : List (Nat × Nat × Nat) := [(3695715328,104424035340936,104424418211701),(3695831040,104424432446013,104424815317005)]
theorem point_links_checked28166 : (cuts28166.take 2).map (fun c => (3695706113-1+2*2^9*c.k,104424003276486+c.lower,104424386147233+c.upper)) = pointBounds28166 := by
 decide +kernel
def cuts28167 : List PrefixCut := [⟨107,389628738,389628951⟩,
⟨128,463577676,463577929⟩]
theorem checked28167 : checkPrefixCuts (2^48) 3695837185 9 Manual.Count131072.C028167.packed 128 cuts28167 = true := by
 decide +kernel
def pointBounds28167 : List (Nat × Nat × Nat) := [(3695946752,104424843704206,104425226575423)]
theorem point_links_checked28167 : (cuts28167.take 1).map (fun c => (3695837185-1+2*2^9*c.k,104424454075468+c.lower,104424836946472+c.upper)) = pointBounds28167 := by
 decide +kernel
def cuts28168 : List PrefixCut := [⟨92,324121284,324121465⟩,
⟨128,455488607,455488859⟩]
theorem checked28168 : checkPrefixCuts (2^48) 3695968257 9 Manual.Count131072.C028168.packed 128 cuts28168 = true := by
 decide +kernel
def pointBounds28168 : List (Nat × Nat × Nat) := [(3696062464,104425241774428,104425624645866)]
theorem point_links_checked28168 : (cuts28168.take 1).map (fun c => (3695968257-1+2*2^9*c.k,104424917653144+c.lower,104425300524401+c.upper)) = pointBounds28168 := by
 decide +kernel
def cuts28169 : List PrefixCut := [⟨77,273011281,273011436⟩,
⟨128,454710954,454711209⟩]
theorem checked28169 : checkPrefixCuts (2^48) 3696099329 9 Manual.Count131072.C028169.packed 128 cuts28169 = true := by
 decide +kernel
def pointBounds28169 : List (Nat × Nat × Nat) := [(3696178176,104425646153032,104426029024696)]
theorem point_links_checked28169 : (cuts28169.take 1).map (fun c => (3696099329-1+2*2^9*c.k,104425373141751+c.lower,104425756013260+c.upper)) = pointBounds28169 := by
 decide +kernel
def cuts28170 : List PrefixCut := [⟨62,219087084,219087203⟩,
⟨128,449821199,449821447⟩]
theorem checked28170 : checkPrefixCuts (2^48) 3696230401 9 Manual.Count131072.C028170.packed 128 cuts28170 = true := by
 decide +kernel
def pointBounds28170 : List (Nat × Nat × Nat) := [(3696293888,104426046939789,104426429811672)]
theorem point_links_checked28170 : (cuts28170.take 1).map (fun c => (3696230401-1+2*2^9*c.k,104425827852705+c.lower,104426210724469+c.upper)) = pointBounds28170 := by
 decide +kernel
def cuts28171 : List PrefixCut := [⟨47,167679398,167679492⟩,
⟨128,452622740,452622996⟩]
theorem checked28171 : checkPrefixCuts (2^48) 3696361473 9 Manual.Count131072.C028171.packed 128 cuts28171 = true := by
 decide +kernel
def pointBounds28171 : List (Nat × Nat × Nat) := [(3696409600,104426445353302,104426828225408)]
theorem point_links_checked28171 : (cuts28171.take 1).map (fun c => (3696361473-1+2*2^9*c.k,104426277673904+c.lower,104426660545916+c.upper)) = pointBounds28171 := by
 decide +kernel
def cuts28172 : List PrefixCut := [⟨32,110640354,110640415⟩,
⟨128,445220601,445220853⟩]
theorem checked28172 : checkPrefixCuts (2^48) 3696492545 9 Manual.Count131072.C028172.packed 128 cuts28172 = true := by
 decide +kernel
def pointBounds28172 : List (Nat × Nat × Nat) := [(3696525312,104426840936998,104427223809327)]
theorem point_links_checked28172 : (cuts28172.take 1).map (fun c => (3696492545-1+2*2^9*c.k,104426730296644+c.lower,104427113168912+c.upper)) = pointBounds28172 := by
 decide +kernel
def cuts28173 : List PrefixCut := [⟨17,58478294,58478327⟩,
⟨128,454417990,454418247⟩]
theorem checked28173 : checkPrefixCuts (2^48) 3696623617 9 Manual.Count131072.C028173.packed 128 cuts28173 = true := by
 decide +kernel
def pointBounds28173 : List (Nat × Nat × Nat) := [(3696641024,104427233995539,104427616868092)]
theorem point_links_checked28173 : (cuts28173.take 1).map (fun c => (3696623617-1+2*2^9*c.k,104427175517245+c.lower,104427558389765+c.upper)) = pointBounds28173 := by
 decide +kernel
def cuts28174 : List PrefixCut := [⟨2,6471990,6471993⟩,
⟨115,401104846,401105073⟩,
⟨128,448539142,448539397⟩]
theorem checked28174 : checkPrefixCuts (2^48) 3696754689 9 Manual.Count131072.C028174.packed 128 cuts28174 = true := by
 decide +kernel
def pointBounds28174 : List (Nat × Nat × Nat) := [(3696756736,104427636407225,104428019280005),(3696872448,104428031040081,104428413913085)]
theorem point_links_checked28174 : (cuts28174.take 2).map (fun c => (3696754689-1+2*2^9*c.k,104427629935235+c.lower,104428012808012+c.upper)) = pointBounds28174 := by
 decide +kernel
def cuts28175 : List PrefixCut := [⟨100,351297611,351297805⟩,
⟨128,448218711,448218961⟩]
theorem checked28175 : checkPrefixCuts (2^48) 3696885761 9 Manual.Count131072.C028175.packed 128 cuts28175 = true := by
 decide +kernel
def pointBounds28175 : List (Nat × Nat × Nat) := [(3696988160,104428429771988,104428812645214)]
theorem point_links_checked28175 : (cuts28175.take 1).map (fun c => (3696885761-1+2*2^9*c.k,104428078474377+c.lower,104428461347409+c.upper)) = pointBounds28175 := by
 decide +kernel
def cuts28176 : List PrefixCut := [⟨85,299818800,299818966⟩,
⟨128,450182353,450182599⟩]
theorem checked28176 : checkPrefixCuts (2^48) 3697016833 9 Manual.Count131072.C028176.packed 128 cuts28176 = true := by
 decide +kernel
def pointBounds28176 : List (Nat × Nat × Nat) := [(3697103872,104428826511888,104429209385336)]
theorem point_links_checked28176 : (cuts28176.take 1).map (fun c => (3697016833-1+2*2^9*c.k,104428526693088+c.lower,104428909566370+c.upper)) = pointBounds28176 := by
 decide +kernel
def cuts28177 : List PrefixCut := [⟨70,248343359,248343498⟩,
⟨128,455647784,455648040⟩]
theorem checked28177 : checkPrefixCuts (2^48) 3697147905 9 Manual.Count131072.C028177.packed 128 cuts28177 = true := by
 decide +kernel
def pointBounds28177 : List (Nat × Nat × Nat) := [(3697219584,104429225218800,104429608092467)]
theorem point_links_checked28177 : (cuts28177.take 1).map (fun c => (3697147905-1+2*2^9*c.k,104428976875441+c.lower,104429359748969+c.upper)) = pointBounds28177 := by
 decide +kernel
def cuts28178 : List PrefixCut := [⟨55,192988790,192988898⟩,
⟨128,451825208,451825461⟩]
theorem checked28178 : checkPrefixCuts (2^48) 3697278977 9 Manual.Count131072.C028178.packed 128 cuts28178 = true := by
 decide +kernel
def pointBounds28178 : List (Nat × Nat × Nat) := [(3697335296,104429625512015,104430008385907)]
theorem point_links_checked28178 : (cuts28178.take 1).map (fun c => (3697278977-1+2*2^9*c.k,104429432523225+c.lower,104429815397009+c.upper)) = pointBounds28178 := by
 decide +kernel
def cuts28179 : List PrefixCut := [⟨40,143119066,143119146⟩,
⟨128,449525453,449525707⟩]
theorem checked28179 : checkPrefixCuts (2^48) 3697410049 9 Manual.Count131072.C028179.packed 128 cuts28179 = true := by
 decide +kernel
def pointBounds28179 : List (Nat × Nat × Nat) := [(3697451008,104430027467499,104430410341616)]
theorem point_links_checked28179 : (cuts28179.take 1).map (fun c => (3697410049-1+2*2^9*c.k,104429884348433+c.lower,104430267222470+c.upper)) = pointBounds28179 := by
 decide +kernel
def cuts28180 : List PrefixCut := [⟨25,86325324,86325374⟩,
⟨128,449509492,449509744⟩]
theorem checked28180 : checkPrefixCuts (2^48) 3697541121 9 Manual.Count131072.C028180.packed 128 cuts28180 = true := by
 decide +kernel
def pointBounds28180 : List (Nat × Nat × Nat) := [(3697566720,104430420199210,104430803073551)]
theorem point_links_checked28180 : (cuts28180.take 1).map (fun c => (3697541121-1+2*2^9*c.k,104430333873886+c.lower,104430716748177+c.upper)) = pointBounds28180 := by
 decide +kernel
def cuts28181 : List PrefixCut := [⟨10,35320648,35320669⟩,
⟨123,440207081,440207321⟩,
⟨128,458628011,458628261⟩]
theorem checked28181 : checkPrefixCuts (2^48) 3697672193 9 Manual.Count131072.C028181.packed 128 cuts28181 = true := by
 decide +kernel
def pointBounds28181 : List (Nat × Nat × Nat) := [(3697682432,104430818704026,104431201578590),(3697798144,104431223590459,104431606465242)]
theorem point_links_checked28181 : (cuts28181.take 2).map (fun c => (3697672193-1+2*2^9*c.k,104430783383378+c.lower,104431166257921+c.upper)) = pointBounds28181 := by
 decide +kernel
def cuts28182 : List PrefixCut := [⟨108,385158888,385159105⟩,
⟨128,455490995,455491250⟩]
theorem checked28182 : checkPrefixCuts (2^48) 3697803265 9 Manual.Count131072.C028182.packed 128 cuts28182 = true := by
 decide +kernel
def pointBounds28182 : List (Nat × Nat × Nat) := [(3697913856,104431627170277,104432010045287)]
theorem point_links_checked28182 : (cuts28182.take 1).map (fun c => (3697803265-1+2*2^9*c.k,104431242011389+c.lower,104431624886182+c.upper)) = pointBounds28182 := by
 decide +kernel
def cuts28183 : List PrefixCut := [⟨93,335214068,335214256⟩,
⟨128,454257082,454257338⟩]
theorem checked28183 : checkPrefixCuts (2^48) 3697934337 9 Manual.Count131072.C028183.packed 128 cuts28183 = true := by
 decide +kernel
def pointBounds28183 : List (Nat × Nat × Nat) := [(3698029568,104432032716452,104432415591688)]
theorem point_links_checked28183 : (cuts28183.take 1).map (fun c => (3697934337-1+2*2^9*c.k,104431697502384+c.lower,104432080377432+c.upper)) = pointBounds28183 := by
 decide +kernel
def cuts28184 : List PrefixCut := [⟨78,272104941,272105097⟩,
⟨128,448151811,448152067⟩]
theorem checked28184 : checkPrefixCuts (2^48) 3698065409 9 Manual.Count131072.C028184.packed 128 cuts28184 = true := by
 decide +kernel
def pointBounds28184 : List (Nat × Nat × Nat) := [(3698145280,104432423864407,104432806739867)]
theorem point_links_checked28184 : (cuts28184.take 1).map (fun c => (3698065409-1+2*2^9*c.k,104432151759466+c.lower,104432534634770+c.upper)) = pointBounds28184 := by
 decide +kernel
def cuts28185 : List PrefixCut := [⟨63,227266649,227266776⟩,
⟨128,456584200,456584453⟩]
theorem checked28185 : checkPrefixCuts (2^48) 3698196481 9 Manual.Count131072.C028185.packed 128 cuts28185 = true := by
 decide +kernel
def pointBounds28185 : List (Nat × Nat × Nat) := [(3698260992,104432827177926,104433210053613)]
theorem point_links_checked28185 : (cuts28185.take 1).map (fun c => (3698196481-1+2*2^9*c.k,104432599911277+c.lower,104432982786837+c.upper)) = pointBounds28185 := by
 decide +kernel
def cuts28186 : List PrefixCut := [⟨48,168960184,168960276⟩,
⟨128,450022731,450022982⟩]
theorem checked28186 : checkPrefixCuts (2^48) 3698327553 9 Manual.Count131072.C028186.packed 128 cuts28186 = true := by
 decide +kernel
def pointBounds28186 : List (Nat × Nat × Nat) := [(3698376704,104433225455661,104433608331566)]
theorem point_links_checked28186 : (cuts28186.take 1).map (fun c => (3698327553-1+2*2^9*c.k,104433056495477+c.lower,104433439371290+c.upper)) = pointBounds28186 := by
 decide +kernel
def cuts28187 : List PrefixCut := [⟨33,114234593,114234658⟩,
⟨128,451985537,451985790⟩]
theorem checked28187 : checkPrefixCuts (2^48) 3698458625 9 Manual.Count131072.C028187.packed 128 cuts28187 = true := by
 decide +kernel
def pointBounds28187 : List (Nat × Nat × Nat) := [(3698492416,104433620752801,104434003628930)]
theorem point_links_checked28187 : (cuts28187.take 1).map (fun c => (3698458625-1+2*2^9*c.k,104433506518208+c.lower,104433889394272+c.upper)) = pointBounds28187 := by
 decide +kernel
def cuts28188 : List PrefixCut := [⟨18,65296473,65296509⟩,
⟨128,454937529,454937781⟩]
theorem checked28188 : checkPrefixCuts (2^48) 3698589697 9 Manual.Count131072.C028188.packed 128 cuts28188 = true := by
 decide +kernel
def pointBounds28188 : List (Nat × Nat × Nat) := [(3698608128,104434023800218,104434406676571)]
theorem point_links_checked28188 : (cuts28188.take 1).map (fun c => (3698589697-1+2*2^9*c.k,104433958503745+c.lower,104434341380062+c.upper)) = pointBounds28188 := by
 decide +kernel
def cuts28189 : List PrefixCut := [⟨3,9588672,9588678⟩,
⟨116,411164975,411165204⟩,
⟨128,455301836,455302089⟩]
theorem checked28189 : checkPrefixCuts (2^48) 3698720769 9 Manual.Count131072.C028189.packed 128 cuts28189 = true := by
 decide +kernel
def pointBounds28189 : List (Nat × Nat × Nat) := [(3698723840,104434423029946,104434805906521),(3698839552,104434824606249,104435207483047)]
theorem point_links_checked28189 : (cuts28189.take 2).map (fun c => (3698720769-1+2*2^9*c.k,104434413441274+c.lower,104434796317843+c.upper)) = pointBounds28189 := by
 decide +kernel
def cuts28190 : List PrefixCut := [⟨101,358568369,358568570⟩,
⟨128,455742319,455742574⟩]
theorem checked28190 : checkPrefixCuts (2^48) 3698851841 9 Manual.Count131072.C028190.packed 128 cuts28190 = true := by
 decide +kernel
def pointBounds28190 : List (Nat × Nat × Nat) := [(3698955264,104435227311479,104435610188502)]
theorem point_links_checked28190 : (cuts28190.take 1).map (fun c => (3698851841-1+2*2^9*c.k,104434868743110+c.lower,104435251619932+c.upper)) = pointBounds28190 := by
 decide +kernel
def cuts28191 : List PrefixCut := [⟨86,301942231,301942401⟩,
⟨128,449714776,449715030⟩]
theorem checked28191 : checkPrefixCuts (2^48) 3698982913 9 Manual.Count131072.C028191.packed 128 cuts28191 = true := by
 decide +kernel
def pointBounds28191 : List (Nat × Nat × Nat) := [(3699070976,104435626427660,104436009304907)]
theorem point_links_checked28191 : (cuts28191.take 1).map (fun c => (3698982913-1+2*2^9*c.k,104435324485429+c.lower,104435707362506+c.upper)) = pointBounds28191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000255
