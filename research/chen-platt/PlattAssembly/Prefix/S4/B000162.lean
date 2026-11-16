import PlattAssemblyKernel
import PlattCertificates.Count131072.C035184
import PlattCertificates.Count131072.C035185
import PlattCertificates.Count131072.C035186
import PlattCertificates.Count131072.C035187
import PlattCertificates.Count131072.C035188
import PlattCertificates.Count131072.C035189
import PlattCertificates.Count131072.C035190
import PlattCertificates.Count131072.C035191
import PlattCertificates.Count131072.C035192
import PlattCertificates.Count131072.C035193
import PlattCertificates.Count131072.C035194
import PlattCertificates.Count131072.C035195
import PlattCertificates.Count131072.C035196
import PlattCertificates.Count131072.C035197
import PlattCertificates.Count131072.C035198
import PlattCertificates.Count131072.C035199
import PlattCertificates.Count131072.C035200
import PlattCertificates.Count131072.C035201
import PlattCertificates.Count131072.C035202
import PlattCertificates.Count131072.C035203
import PlattCertificates.Count131072.C035204
import PlattCertificates.Count131072.C035205
import PlattCertificates.Count131072.C035206
import PlattCertificates.Count131072.C035207
import PlattCertificates.Count131072.C035208
import PlattCertificates.Count131072.C035209
import PlattCertificates.Count131072.C035210
import PlattCertificates.Count131072.C035211
import PlattCertificates.Count131072.C035212
import PlattCertificates.Count131072.C035213
import PlattCertificates.Count131072.C035214
import PlattCertificates.Count131072.C035215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35184 : List PrefixCut := [⟨58,333089155,333089368⟩,
⟨64,366690311,366690545⟩]
theorem checked35184 : checkPrefixCuts (2^48) 4615569409 10 Manual.Count131072.C035184.packed 64 cuts35184 = true := by
 decide +kernel
def pointBounds35184 : List (Nat × Nat × Nat) := [(4615688192,107249794843554,107250179367563)]
theorem point_links_checked35184 : (cuts35184.take 1).map (fun c => (4615569409-1+2*2^10*c.k,107249461754399+c.lower,107249846278195+c.upper)) = pointBounds35184 := by
 decide +kernel
def cuts35185 : List PrefixCut := [⟨64,359728017,359728238⟩]
theorem checked35185 : checkPrefixCuts (2^48) 4615700481 10 Manual.Count131072.C035185.packed 64 cuts35185 = true := by
 decide +kernel
def cuts35186 : List PrefixCut := [⟨1,5427247,5427251⟩,
⟨64,352827134,352827356⟩]
theorem checked35186 : checkPrefixCuts (2^48) 4615831553 10 Manual.Count131072.C035186.packed 64 cuts35186 = true := by
 decide +kernel
def pointBounds35186 : List (Nat × Nat × Nat) := [(4615833600,107250193599974,107250578124229)]
theorem point_links_checked35186 : (cuts35186.take 1).map (fun c => (4615831553-1+2*2^10*c.k,107250188172727+c.lower,107250572696978+c.upper)) = pointBounds35186 := by
 decide +kernel
def cuts35187 : List PrefixCut := [⟨8,45733861,45733889⟩,
⟨64,363000387,363000610⟩]
theorem checked35187 : checkPrefixCuts (2^48) 4615962625 10 Manual.Count131072.C035187.packed 64 cuts35187 = true := by
 decide +kernel
def pointBounds35187 : List (Nat × Nat × Nat) := [(4615979008,107250586733722,107250971258223)]
theorem point_links_checked35187 : (cuts35187.take 1).map (fun c => (4615962625-1+2*2^10*c.k,107250540999861+c.lower,107250925524334+c.upper)) = pointBounds35187 := by
 decide +kernel
def cuts35188 : List PrefixCut := [⟨15,86647826,86647883⟩,
⟨64,361099879,361100107⟩]
theorem checked35188 : checkPrefixCuts (2^48) 4616093697 10 Manual.Count131072.C035188.packed 64 cuts35188 = true := by
 decide +kernel
def pointBounds35188 : List (Nat × Nat × Nat) := [(4616124416,107250990648074,107251375172827)]
theorem point_links_checked35188 : (cuts35188.take 1).map (fun c => (4616093697-1+2*2^10*c.k,107250904000248+c.lower,107251288524944+c.upper)) = pointBounds35188 := by
 decide +kernel
def cuts35189 : List PrefixCut := [⟨22,123535008,123535085⟩,
⟨64,357614033,357614258⟩]
theorem checked35189 : checkPrefixCuts (2^48) 4616224769 10 Manual.Count131072.C035189.packed 64 cuts35189 = true := by
 decide +kernel
def pointBounds35189 : List (Nat × Nat × Nat) := [(4616269824,107251388635135,107251773160136)]
theorem point_links_checked35189 : (cuts35189.take 1).map (fun c => (4616224769-1+2*2^10*c.k,107251265100127+c.lower,107251649625051+c.upper)) = pointBounds35189 := by
 decide +kernel
def cuts35190 : List PrefixCut := [⟨29,162310121,162310221⟩,
⟨64,359433045,359433267⟩]
theorem checked35190 : checkPrefixCuts (2^48) 4616355841 10 Manual.Count131072.C035190.packed 64 cuts35190 = true := by
 decide +kernel
def pointBounds35190 : List (Nat × Nat × Nat) := [(4616415232,107251785024281,107252169549530)]
theorem point_links_checked35190 : (cuts35190.take 1).map (fun c => (4616355841-1+2*2^10*c.k,107251622714160+c.lower,107252007239309+c.upper)) = pointBounds35190 := by
 decide +kernel
def cuts35191 : List PrefixCut := [⟨36,201082930,201083057⟩,
⟨64,355642664,355642886⟩]
theorem checked35191 : checkPrefixCuts (2^48) 4616486913 10 Manual.Count131072.C035191.packed 64 cuts35191 = true := by
 decide +kernel
def pointBounds35191 : List (Nat × Nat × Nat) := [(4616560640,107252183230135,107252567755633)]
theorem point_links_checked35191 : (cuts35191.take 1).map (fun c => (4616486913-1+2*2^10*c.k,107251982147205+c.lower,107252366672576+c.upper)) = pointBounds35191 := by
 decide +kernel
def cuts35192 : List PrefixCut := [⟨43,236561062,236561210⟩,
⟨64,354413146,354413367⟩]
theorem checked35192 : checkPrefixCuts (2^48) 4616617985 10 Manual.Count131072.C035192.packed 64 cuts35192 = true := by
 decide +kernel
def pointBounds35192 : List (Nat × Nat × Nat) := [(4616706048,107252574350931,107252958876672)]
theorem point_links_checked35192 : (cuts35192.take 1).map (fun c => (4616617985-1+2*2^10*c.k,107252337789869+c.lower,107252722315462+c.upper)) = pointBounds35192 := by
 decide +kernel
def cuts35193 : List PrefixCut := [⟨50,284352553,284352733⟩,
⟨64,363975009,363975238⟩]
theorem checked35193 : checkPrefixCuts (2^48) 4616749057 10 Manual.Count131072.C035193.packed 64 cuts35193 = true := by
 decide +kernel
def pointBounds35193 : List (Nat × Nat × Nat) := [(4616851456,107252976555568,107253361081562)]
theorem point_links_checked35193 : (cuts35193.take 1).map (fun c => (4616749057-1+2*2^10*c.k,107252692203015+c.lower,107253076728829+c.upper)) = pointBounds35193 := by
 decide +kernel
def cuts35194 : List PrefixCut := [⟨57,320984407,320984607⟩,
⟨64,360306725,360306950⟩]
theorem checked35194 : checkPrefixCuts (2^48) 4616880129 10 Manual.Count131072.C035194.packed 64 cuts35194 = true := by
 decide +kernel
def pointBounds35194 : List (Nat × Nat × Nat) := [(4616996864,107253377162431,107253761688674)]
theorem point_links_checked35194 : (cuts35194.take 1).map (fun c => (4616880129-1+2*2^10*c.k,107253056178024+c.lower,107253440704067+c.upper)) = pointBounds35194 := by
 decide +kernel
def cuts35195 : List PrefixCut := [⟨64,360906186,360906408⟩]
theorem checked35195 : checkPrefixCuts (2^48) 4617011201 10 Manual.Count131072.C035195.packed 64 cuts35195 = true := by
 decide +kernel
def pointBounds35195 : List (Nat × Nat × Nat) := [(4617142272,107253777390935,107254161917425)]
theorem point_links_checked35195 : (cuts35195.take 1).map (fun c => (4617011201-1+2*2^10*c.k,107253416484749+c.lower,107253801011017+c.upper)) = pointBounds35195 := by
 decide +kernel
def cuts35196 : List PrefixCut := [⟨64,357055288,357055512⟩]
theorem checked35196 : checkPrefixCuts (2^48) 4617142273 10 Manual.Count131072.C035196.packed 64 cuts35196 = true := by
 decide +kernel
def cuts35197 : List PrefixCut := [⟨7,37247283,37247306⟩,
⟨64,359727396,359727615⟩]
theorem checked35197 : checkPrefixCuts (2^48) 4617273345 10 Manual.Count131072.C035197.packed 64 cuts35197 = true := by
 decide +kernel
def pointBounds35197 : List (Nat × Nat × Nat) := [(4617287680,107254171693506,107254556220243)]
theorem point_links_checked35197 : (cuts35197.take 1).map (fun c => (4617273345-1+2*2^10*c.k,107254134446223+c.lower,107254518972937+c.upper)) = pointBounds35197 := by
 decide +kernel
def cuts35198 : List PrefixCut := [⟨14,76930711,76930756⟩,
⟨64,357522655,357522878⟩]
theorem checked35198 : checkPrefixCuts (2^48) 4617404417 10 Manual.Count131072.C035198.packed 64 cuts35198 = true := by
 decide +kernel
def pointBounds35198 : List (Nat × Nat × Nat) := [(4617433088,107254571104330,107254955631308)]
theorem point_links_checked35198 : (cuts35198.take 1).map (fun c => (4617404417-1+2*2^10*c.k,107254494173619+c.lower,107254878700552+c.upper)) = pointBounds35198 := by
 decide +kernel
def cuts35199 : List PrefixCut := [⟨21,117465166,117465238⟩,
⟨64,356171468,356171692⟩]
theorem checked35199 : checkPrefixCuts (2^48) 4617535489 10 Manual.Count131072.C035199.packed 64 cuts35199 = true := by
 decide +kernel
def pointBounds35199 : List (Nat × Nat × Nat) := [(4617578496,107254969161440,107255353688668)]
theorem point_links_checked35199 : (cuts35199.take 1).map (fun c => (4617535489-1+2*2^10*c.k,107254851696274+c.lower,107255236223430+c.upper)) = pointBounds35199 := by
 decide +kernel
def cuts35200 : List PrefixCut := [⟨28,156290448,156290550⟩,
⟨64,360123434,360123660⟩]
theorem checked35200 : checkPrefixCuts (2^48) 4617666561 10 Manual.Count131072.C035200.packed 64 cuts35200 = true := by
 decide +kernel
def pointBounds35200 : List (Nat × Nat × Nat) := [(4617723904,107255364158190,107255748685672)]
theorem point_links_checked35200 : (cuts35200.take 1).map (fun c => (4617666561-1+2*2^10*c.k,107255207867742+c.lower,107255592395122+c.upper)) = pointBounds35200 := by
 decide +kernel
def cuts35201 : List PrefixCut := [⟨35,199563043,199563166⟩,
⟨64,364379999,364380222⟩]
theorem checked35201 : checkPrefixCuts (2^48) 4617797633 10 Manual.Count131072.C035201.packed 64 cuts35201 = true := by
 decide +kernel
def pointBounds35201 : List (Nat × Nat × Nat) := [(4617869312,107255767554219,107256152081948)]
theorem point_links_checked35201 : (cuts35201.take 1).map (fun c => (4617797633-1+2*2^10*c.k,107255567991176+c.lower,107255952518782+c.upper)) = pointBounds35201 := by
 decide +kernel
def cuts35202 : List PrefixCut := [⟨42,232958779,232958924⟩,
⟨64,355775428,355775651⟩]
theorem checked35202 : checkPrefixCuts (2^48) 4617928705 10 Manual.Count131072.C035202.packed 64 cuts35202 = true := by
 decide +kernel
def pointBounds35202 : List (Nat × Nat × Nat) := [(4618014720,107256165329954,107256549857928)]
theorem point_links_checked35202 : (cuts35202.take 1).map (fun c => (4617928705-1+2*2^10*c.k,107255932371175+c.lower,107256316899004+c.upper)) = pointBounds35202 := by
 decide +kernel
def cuts35203 : List PrefixCut := [⟨49,271228566,271228730⟩,
⟨64,356679583,356679803⟩]
theorem checked35203 : checkPrefixCuts (2^48) 4618059777 10 Manual.Count131072.C035203.packed 64 cuts35203 = true := by
 decide +kernel
def pointBounds35203 : List (Nat × Nat × Nat) := [(4618160128,107256559375169,107256943903385)]
theorem point_links_checked35203 : (cuts35203.take 1).map (fun c => (4618059777-1+2*2^10*c.k,107256288146603+c.lower,107256672674655+c.upper)) = pointBounds35203 := by
 decide +kernel
def cuts35204 : List PrefixCut := [⟨56,317114582,317114786⟩,
⟨64,361240607,361240838⟩]
theorem checked35204 : checkPrefixCuts (2^48) 4618190849 10 Manual.Count131072.C035204.packed 64 cuts35204 = true := by
 decide +kernel
def pointBounds35204 : List (Nat × Nat × Nat) := [(4618305536,107256961940768,107257346469244)]
theorem point_links_checked35204 : (cuts35204.take 1).map (fun c => (4618190849-1+2*2^10*c.k,107256644826186+c.lower,107257029354458+c.upper)) = pointBounds35204 := by
 decide +kernel
def cuts35205 : List PrefixCut := [⟨63,352271302,352271514⟩,
⟨64,357390743,357390958⟩]
theorem checked35205 : checkPrefixCuts (2^48) 4618321921 10 Manual.Count131072.C035205.packed 64 cuts35205 = true := by
 decide +kernel
def pointBounds35205 : List (Nat × Nat × Nat) := [(4618450944,107257358338095,107257742866810)]
theorem point_links_checked35205 : (cuts35205.take 1).map (fun c => (4618321921-1+2*2^10*c.k,107257006066793+c.lower,107257390595296+c.upper)) = pointBounds35205 := by
 decide +kernel
def cuts35206 : List PrefixCut := [⟨64,362438960,362439186⟩]
theorem checked35206 : checkPrefixCuts (2^48) 4618452993 10 Manual.Count131072.C035206.packed 64 cuts35206 = true := by
 decide +kernel
def cuts35207 : List PrefixCut := [⟨6,33214424,33214444⟩,
⟨64,357675152,357675376⟩]
theorem checked35207 : checkPrefixCuts (2^48) 4618584065 10 Manual.Count131072.C035207.packed 64 cuts35207 = true := by
 decide +kernel
def pointBounds35207 : List (Nat × Nat × Nat) := [(4618596352,107257759110920,107258143639884)]
theorem point_links_checked35207 : (cuts35207.take 1).map (fun c => (4618584065-1+2*2^10*c.k,107257725896496+c.lower,107258110425440+c.upper)) = pointBounds35207 := by
 decide +kernel
def cuts35208 : List PrefixCut := [⟨13,74227445,74227492⟩,
⟨64,363698192,363698419⟩]
theorem checked35208 : checkPrefixCuts (2^48) 4618715137 10 Manual.Count131072.C035208.packed 64 cuts35208 = true := by
 decide +kernel
def pointBounds35208 : List (Nat × Nat × Nat) := [(4618741760,107258157799093,107258542328308)]
theorem point_links_checked35208 : (cuts35208.take 1).map (fun c => (4618715137-1+2*2^10*c.k,107258083571648+c.lower,107258468100816+c.upper)) = pointBounds35208 := by
 decide +kernel
def cuts35209 : List PrefixCut := [⟨20,114994245,114994316⟩,
⟨64,360519015,360519238⟩]
theorem checked35209 : checkPrefixCuts (2^48) 4618846209 10 Manual.Count131072.C035209.packed 64 cuts35209 = true := by
 decide +kernel
def pointBounds35209 : List (Nat × Nat × Nat) := [(4618887168,107258562264085,107258946793551)]
theorem point_links_checked35209 : (cuts35209.take 1).map (fun c => (4618846209-1+2*2^10*c.k,107258447269840+c.lower,107258831799235+c.upper)) = pointBounds35209 := by
 decide +kernel
def cuts35210 : List PrefixCut := [⟨27,150517924,150518016⟩,
⟨64,355999397,355999619⟩]
theorem checked35210 : checkPrefixCuts (2^48) 4618977281 10 Manual.Count131072.C035210.packed 64 cuts35210 = true := by
 decide +kernel
def pointBounds35210 : List (Nat × Nat × Nat) := [(4619032576,107258958306779,107259342836489)]
theorem point_links_checked35210 : (cuts35210.take 1).map (fun c => (4618977281-1+2*2^10*c.k,107258807788855+c.lower,107259192318473+c.upper)) = pointBounds35210 := by
 decide +kernel
def cuts35211 : List PrefixCut := [⟨34,191889349,191889466⟩,
⟨64,358122044,358122270⟩]
theorem checked35211 : checkPrefixCuts (2^48) 4619108353 10 Manual.Count131072.C035211.packed 64 cuts35211 = true := by
 decide +kernel
def pointBounds35211 : List (Nat × Nat × Nat) := [(4619177984,107259355677601,107259740207558)]
theorem point_links_checked35211 : (cuts35211.take 1).map (fun c => (4619108353-1+2*2^10*c.k,107259163788252+c.lower,107259548318092+c.upper)) = pointBounds35211 := by
 decide +kernel
def cuts35212 : List PrefixCut := [⟨41,231491239,231491384⟩,
⟨64,361828889,361829114⟩]
theorem checked35212 : checkPrefixCuts (2^48) 4619239425 10 Manual.Count131072.C035212.packed 64 cuts35212 = true := by
 decide +kernel
def pointBounds35212 : List (Nat × Nat × Nat) := [(4619323392,107259753401535,107260137931746)]
theorem point_links_checked35212 : (cuts35212.take 1).map (fun c => (4619239425-1+2*2^10*c.k,107259521910296+c.lower,107259906440362+c.upper)) = pointBounds35212 := by
 decide +kernel
def cuts35213 : List PrefixCut := [⟨48,268104990,268105156⟩,
⟨64,356517456,356517678⟩]
theorem checked35213 : checkPrefixCuts (2^48) 4619370497 10 Manual.Count131072.C035213.packed 64 cuts35213 = true := by
 decide +kernel
def pointBounds35213 : List (Nat × Nat × Nat) := [(4619468800,107260151844175,107260536374632)]
theorem point_links_checked35213 : (cuts35213.take 1).map (fun c => (4619370497-1+2*2^10*c.k,107259883739185+c.lower,107260268269476+c.upper)) = pointBounds35213 := by
 decide +kernel
def cuts35214 : List PrefixCut := [⟨55,307580363,307580550⟩,
⟨64,359310159,359310378⟩]
theorem checked35214 : checkPrefixCuts (2^48) 4619501569 10 Manual.Count131072.C035214.packed 64 cuts35214 = true := by
 decide +kernel
def pointBounds35214 : List (Nat × Nat × Nat) := [(4619614208,107260547837004,107260932367704)]
theorem point_links_checked35214 : (cuts35214.take 1).map (fun c => (4619501569-1+2*2^10*c.k,107260240256641+c.lower,107260624787154+c.upper)) = pointBounds35214 := by
 decide +kernel
def cuts35215 : List PrefixCut := [⟨62,350891872,350892092⟩,
⟨64,361919921,361920147⟩]
theorem checked35215 : checkPrefixCuts (2^48) 4619632641 10 Manual.Count131072.C035215.packed 64 cuts35215 = true := by
 decide +kernel
def pointBounds35215 : List (Nat × Nat × Nat) := [(4619759616,107260950458672,107261334989624)]
theorem point_links_checked35215 : (cuts35215.take 1).map (fun c => (4619632641-1+2*2^10*c.k,107260599566800+c.lower,107260984097532+c.upper)) = pointBounds35215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000162
