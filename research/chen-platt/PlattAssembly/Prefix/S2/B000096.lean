import PlattAssemblyKernel
import PlattCertificates.Count131072.C013072
import PlattCertificates.Count131072.C013073
import PlattCertificates.Count131072.C013074
import PlattCertificates.Count131072.C013075
import PlattCertificates.Count131072.C013076
import PlattCertificates.Count131072.C013077
import PlattCertificates.Count131072.C013078
import PlattCertificates.Count131072.C013079
import PlattCertificates.Count131072.C013080
import PlattCertificates.Count131072.C013081
import PlattCertificates.Count131072.C013082
import PlattCertificates.Count131072.C013083
import PlattCertificates.Count131072.C013084
import PlattCertificates.Count131072.C013085
import PlattCertificates.Count131072.C013086
import PlattCertificates.Count131072.C013087
import PlattCertificates.Count131072.C013088
import PlattCertificates.Count131072.C013089
import PlattCertificates.Count131072.C013090
import PlattCertificates.Count131072.C013091
import PlattCertificates.Count131072.C013092
import PlattCertificates.Count131072.C013093
import PlattCertificates.Count131072.C013094
import PlattCertificates.Count131072.C013095
import PlattCertificates.Count131072.C013096
import PlattCertificates.Count131072.C013097
import PlattCertificates.Count131072.C013098
import PlattCertificates.Count131072.C013099
import PlattCertificates.Count131072.C013100
import PlattCertificates.Count131072.C013101
import PlattCertificates.Count131072.C013102
import PlattCertificates.Count131072.C013103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13072 : List PrefixCut := [⟨28,219958648,219958807⟩,
⟨81,642328094,642328561⟩,
⟨128,1013221980,1013222717⟩]
theorem checked13072 : checkPrefixCuts (2^48) 1717305345 9 Manual.Count131072.C013072.packed 128 cuts13072 = true := by
 decide +kernel
def pointBounds13072 : List (Nat × Nat × Nat) := [(1717334016,94457745137856,94458121915900),(1717388288,94458167507302,94458544285654)]
theorem point_links_checked13072 : (cuts13072.take 2).map (fun c => (1717305345-1+2*2^9*c.k,94457525179208+c.lower,94457901957093+c.upper)) = pointBounds13072 := by
 decide +kernel
def cuts13073 : List PrefixCut := [⟨6,48839865,48839901⟩,
⟨59,462332507,462332841⟩,
⟨112,883842454,883843093⟩,
⟨128,1007572396,1007573125⟩]
theorem checked13073 : checkPrefixCuts (2^48) 1717436417 9 Manual.Count131072.C013073.packed 128 cuts13073 = true := by
 decide +kernel
def pointBounds13073 : List (Nat × Nat × Nat) := [(1717442560,94458587241053,94458964019711),(1717496832,94459000733695,94459377512651),(1717551104,94459422243642,94459799022903)]
theorem point_links_checked13073 : (cuts13073.take 3).map (fun c => (1717436417-1+2*2^9*c.k,94458538401188+c.lower,94458915179810+c.upper)) = pointBounds13073 := by
 decide +kernel
def cuts13074 : List PrefixCut := [⟨37,291375320,291375533⟩,
⟨90,713841932,713842455⟩,
⟨128,1007004070,1007004808⟩]
theorem checked13074 : checkPrefixCuts (2^48) 1717567489 9 Manual.Count131072.C013074.packed 128 cuts13074 = true := by
 decide +kernel
def pointBounds13074 : List (Nat × Nat × Nat) := [(1717605376,94459837348904,94460214128468),(1717659648,94460259815516,94460636595390)]
theorem point_links_checked13074 : (cuts13074.take 2).map (fun c => (1717567489-1+2*2^9*c.k,94459545973584+c.lower,94459922752935+c.upper)) = pointBounds13074 := by
 decide +kernel
def cuts13075 : List PrefixCut := [⟨15,116509226,116509311⟩,
⟨68,542062452,542062834⟩,
⟨121,957770690,957771372⟩,
⟨128,1014628472,1014629193⟩]
theorem checked13075 : checkPrefixCuts (2^48) 1717698561 9 Manual.Count131072.C013075.packed 128 cuts13075 = true := by
 decide +kernel
def pointBounds13075 : List (Nat × Nat × Nat) := [(1717713920,94460669486880,94461046267054),(1717768192,94461095040106,94461471820577),(1717822464,94461510748344,94461887529115)]
theorem point_links_checked13075 : (cuts13075.take 3).map (fun c => (1717698561-1+2*2^9*c.k,94460552977654+c.lower,94460929757743+c.upper)) = pointBounds13075 := by
 decide +kernel
def cuts13076 : List PrefixCut := [⟨46,353430304,353430562⟩,
⟨99,771242302,771242862⟩,
⟨128,1004228238,1004228967⟩]
theorem checked13076 : checkPrefixCuts (2^48) 1717829633 9 Manual.Count131072.C013076.packed 128 cuts13076 = true := by
 decide +kernel
def pointBounds13076 : List (Nat × Nat × Nat) := [(1717876736,94461921036430,94462297817498),(1717931008,94462338848428,94462715629798)]
theorem point_links_checked13076 : (cuts13076.take 2).map (fun c => (1717829633-1+2*2^9*c.k,94461567606126+c.lower,94461944386936+c.upper)) = pointBounds13076 := by
 decide +kernel
def cuts13077 : List PrefixCut := [⟨24,186451395,186451531⟩,
⟨77,605220117,605220551⟩,
⟨128,1008903144,1008903875⟩]
theorem checked13077 : checkPrefixCuts (2^48) 1717960705 9 Manual.Count131072.C013077.packed 128 cuts13077 = true := by
 decide +kernel
def pointBounds13077 : List (Nat × Nat × Nat) := [(1717985280,94462758285759,94463135067434),(1718039552,94463177054481,94463553836454)]
theorem point_links_checked13077 : (cuts13077.take 2).map (fun c => (1717960705-1+2*2^9*c.k,94462571834364+c.lower,94462948615903+c.upper)) = pointBounds13077 := by
 decide +kernel
def cuts13078 : List PrefixCut := [⟨2,18021282,18021296⟩,
⟨55,438401719,438402038⟩,
⟨108,862209160,862209787⟩,
⟨128,1020130106,1020130851⟩]
theorem checked13078 : checkPrefixCuts (2^48) 1718091777 9 Manual.Count131072.C013078.packed 128 cuts13078 = true := by
 decide +kernel
def pointBounds13078 : List (Nat × Nat × Nat) := [(1718093824,94463598758790,94463975541074),(1718148096,94464019139227,94464395921816),(1718202368,94464442946668,94464819729565)]
theorem point_links_checked13078 : (cuts13078.take 3).map (fun c => (1718091777-1+2*2^9*c.k,94463580737508+c.lower,94463957519778+c.upper)) = pointBounds13078 := by
 decide +kernel
def cuts13079 : List PrefixCut := [⟨33,255388881,255389065⟩,
⟨86,669177152,669177635⟩,
⟨128,999739639,999740358⟩]
theorem checked13079 : checkPrefixCuts (2^48) 1718222849 9 Manual.Count131072.C013079.packed 128 cuts13079 = true := by
 decide +kernel
def pointBounds13079 : List (Nat × Nat × Nat) := [(1718256640,94464856256495,94465233039694),(1718310912,94465270044766,94465646828264)]
theorem point_links_checked13079 : (cuts13079.take 2).map (fun c => (1718222849-1+2*2^9*c.k,94464600867614+c.lower,94464977650629+c.upper)) = pointBounds13079 := by
 decide +kernel
def cuts13080 : List PrefixCut := [⟨11,89437217,89437281⟩,
⟨64,499104268,499104631⟩,
⟨117,918586196,918586858⟩,
⟨128,1007034419,1007035143⟩]
theorem checked13080 : checkPrefixCuts (2^48) 1718353921 9 Manual.Count131072.C013080.packed 128 cuts13080 = true := by
 decide +kernel
def pointBounds13080 : List (Nat × Nat × Nat) := [(1718365184,94465690044470,94466066828268),(1718419456,94466099711521,94466476495618),(1718473728,94466519193449,94466895977845)]
theorem point_links_checked13080 : (cuts13080.take 3).map (fun c => (1718353921-1+2*2^9*c.k,94465600607253+c.lower,94465977390987+c.upper)) = pointBounds13080 := by
 decide +kernel
def cuts13081 : List PrefixCut := [⟨42,328563512,328563753⟩,
⟨95,749165461,749166009⟩,
⟨128,1007940312,1007941048⟩]
theorem checked13081 : checkPrefixCuts (2^48) 1718484993 9 Manual.Count131072.C013081.packed 128 cuts13081 = true := by
 decide +kernel
def pointBounds13081 : List (Nat × Nat × Nat) := [(1718528000,94466936205184,94467312989883),(1718582272,94467356807133,94467733592139)]
theorem point_links_checked13081 : (cuts13081.take 2).map (fun c => (1718484993-1+2*2^9*c.k,94466607641672+c.lower,94466984426130+c.upper)) = pointBounds13081 := by
 decide +kernel
def cuts13082 : List PrefixCut := [⟨20,155590044,155590157⟩,
⟨73,574200141,574200551⟩,
⟨126,992796990,992797702⟩,
⟨128,1006553466,1006554188⟩]
theorem checked13082 : checkPrefixCuts (2^48) 1718616065 9 Manual.Count131072.C013082.packed 128 cuts13082 = true := by
 decide +kernel
def pointBounds13082 : List (Nat × Nat × Nat) := [(1718636544,94467771172028,94468147957335),(1718690816,94468189782125,94468566567729),(1718745088,94468608378974,94468985164880)]
theorem point_links_checked13082 : (cuts13082.take 3).map (fun c => (1718616065-1+2*2^9*c.k,94467615581984+c.lower,94467992367178+c.upper)) = pointBounds13082 := by
 decide +kernel
def cuts13083 : List PrefixCut := [⟨51,406300844,406301134⟩,
⟨104,825526225,825526814⟩,
⟨128,1015810889,1015811614⟩]
theorem checked13083 : checkPrefixCuts (2^48) 1718747137 9 Manual.Count131072.C013083.packed 128 cuts13083 = true := by
 decide +kernel
def pointBounds13083 : List (Nat × Nat × Nat) := [(1718799360,94469028436294,94469405222500),(1718853632,94469447661675,94469824448180)]
theorem point_links_checked13083 : (cuts13083.take 2).map (fun c => (1718747137-1+2*2^9*c.k,94468622135450+c.lower,94468998921366+c.upper)) = pointBounds13083 := by
 decide +kernel
def cuts13084 : List PrefixCut := [⟨29,230073794,230073960⟩,
⟨82,649927629,649928099⟩,
⟨128,1012622249,1012622985⟩]
theorem checked13084 : checkPrefixCuts (2^48) 1718878209 9 Manual.Count131072.C013084.packed 128 cuts13084 = true := by
 decide +kernel
def pointBounds13084 : List (Nat × Nat × Nat) := [(1718907904,94469868020133,94470244806940),(1718962176,94470287873968,94470664661079)]
theorem point_links_checked13084 : (cuts13084.take 2).map (fun c => (1718878209-1+2*2^9*c.k,94469637946339+c.lower,94470014732980+c.upper)) = pointBounds13084 := by
 decide +kernel
def cuts13085 : List PrefixCut := [⟨7,55017364,55017403⟩,
⟨60,472061215,472061556⟩,
⟨113,890074444,890075088⟩,
⟨128,1014346087,1014346820⟩]
theorem checked13085 : checkPrefixCuts (2^48) 1719009281 9 Manual.Count131072.C013085.packed 128 cuts13085 = true := by
 decide +kernel
def pointBounds13085 : List (Nat × Nat × Nat) := [(1719016448,94470705585952,94471082373368),(1719070720,94471122629803,94471499417521),(1719124992,94471540643032,94471917431053)]
theorem point_links_checked13085 : (cuts13085.take 3).map (fun c => (1719009281-1+2*2^9*c.k,94470650568588+c.lower,94471027355965+c.upper)) = pointBounds13085 := by
 decide +kernel
def cuts13086 : List PrefixCut := [⟨38,293400837,293401049⟩,
⟨91,714825670,714826188⟩,
⟨128,1006900967,1006901693⟩]
theorem checked13086 : checkPrefixCuts (2^48) 1719140353 9 Manual.Count131072.C013086.packed 128 cuts13086 = true := by
 decide +kernel
def pointBounds13086 : List (Nat × Nat × Nat) := [(1719179264,94471958315512,94472335103834),(1719233536,94472379740345,94472756528973)]
theorem point_links_checked13086 : (cuts13086.take 2).map (fun c => (1719140353-1+2*2^9*c.k,94471664914675+c.lower,94472041702785+c.upper)) = pointBounds13086 := by
 decide +kernel
def cuts13087 : List PrefixCut := [⟨16,125407020,125407110⟩,
⟨69,539601945,539602330⟩,
⟨122,959022355,959023040⟩,
⟨128,1005187262,1005187981⟩]
theorem checked13087 : checkPrefixCuts (2^48) 1719271425 9 Manual.Count131072.C013087.packed 128 cuts13087 = true := by
 decide +kernel
def pointBounds13087 : List (Nat × Nat × Nat) := [(1719287808,94472797222662,94473174011588),(1719342080,94473211417587,94473588206808),(1719396352,94473630837997,94474007627518)]
theorem point_links_checked13087 : (cuts13087.take 3).map (fun c => (1719271425-1+2*2^9*c.k,94472671815642+c.lower,94473048604478+c.upper)) = pointBounds13087 := by
 decide +kernel
def cuts13088 : List PrefixCut := [⟨47,376680060,376680335⟩,
⟨100,792963802,792964377⟩,
⟨128,1016897108,1016897848⟩]
theorem checked13088 : checkPrefixCuts (2^48) 1719402497 9 Manual.Count131072.C013088.packed 128 cuts13088 = true := by
 decide +kernel
def pointBounds13088 : List (Nat × Nat × Nat) := [(1719450624,94474053682964,94474430472794),(1719504896,94474469966706,94474846756836)]
theorem point_links_checked13088 : (cuts13088.take 2).map (fun c => (1719402497-1+2*2^9*c.k,94473677002904+c.lower,94474053792459+c.upper)) = pointBounds13088 := by
 decide +kernel
def cuts13089 : List PrefixCut := [⟨25,196102259,196102400⟩,
⟨78,618088656,618089105⟩,
⟨128,1013218284,1013219019⟩]
theorem checked13089 : checkPrefixCuts (2^48) 1719533569 9 Manual.Count131072.C013089.packed 128 cuts13089 = true := by
 decide +kernel
def pointBounds13089 : List (Nat × Nat × Nat) := [(1719559168,94474890002271,94475266792707),(1719613440,94475311988668,94475688779412)]
theorem point_links_checked13089 : (cuts13089.take 2).map (fun c => (1719533569-1+2*2^9*c.k,94474693900012+c.lower,94475070690307+c.upper)) = pointBounds13089 := by
 decide +kernel
def cuts13090 : List PrefixCut := [⟨3,23406233,23406250⟩,
⟨56,443893003,443893327⟩,
⟨109,857492252,857492876⟩,
⟨128,1002338921,1002339650⟩]
theorem checked13090 : checkPrefixCuts (2^48) 1719664641 9 Manual.Count131072.C013090.packed 128 cuts13090 = true := by
 decide +kernel
def pointBounds13090 : List (Nat × Nat × Nat) := [(1719667712,94475730524529,94476107315576),(1719721984,94476151011299,94476527802653),(1719776256,94476564610548,94476941402202)]
theorem point_links_checked13090 : (cuts13090.take 3).map (fun c => (1719664641-1+2*2^9*c.k,94475707118296+c.lower,94476083909326+c.upper)) = pointBounds13090 := by
 decide +kernel
def cuts13091 : List PrefixCut := [⟨34,270212502,270212697⟩,
⟨87,690986855,690987355⟩,
⟨128,1018955744,1018956480⟩]
theorem checked13091 : checkPrefixCuts (2^48) 1719795713 9 Manual.Count131072.C013091.packed 128 cuts13091 = true := by
 decide +kernel
def pointBounds13091 : List (Nat × Nat × Nat) := [(1719830528,94476979669719,94477356461673),(1719884800,94477400444072,94477777236331)]
theorem point_links_checked13091 : (cuts13091.take 2).map (fun c => (1719795713-1+2*2^9*c.k,94476709457217+c.lower,94477086248976+c.upper)) = pointBounds13091 := by
 decide +kernel
def cuts13092 : List PrefixCut := [⟨12,94428684,94428753⟩,
⟨65,516812938,516813312⟩,
⟨118,935910896,935911576⟩,
⟨128,1017732480,1017733219⟩]
theorem checked13092 : checkPrefixCuts (2^48) 1719926785 9 Manual.Count131072.C013092.packed 128 cuts13092 = true := by
 decide +kernel
def pointBounds13092 : List (Nat × Nat × Nat) := [(1719939072,94477822841645,94478199634209),(1719993344,94478245225899,94478622018768),(1720047616,94478664323857,94479041117032)]
theorem point_links_checked13092 : (cuts13092.take 3).map (fun c => (1719926785-1+2*2^9*c.k,94477728412961+c.lower,94478105205456+c.upper)) = pointBounds13092 := by
 decide +kernel
def cuts13093 : List PrefixCut := [⟨43,337426875,337427118⟩,
⟨96,755189403,755189948⟩,
⟨128,1007345977,1007346703⟩]
theorem checked13093 : checkPrefixCuts (2^48) 1720057857 9 Manual.Count131072.C013093.packed 128 cuts13093 = true := by
 decide +kernel
def pointBounds13093 : List (Nat × Nat × Nat) := [(1720101888,94479083572316,94479460365793),(1720156160,94479501334844,94479878128623)]
theorem point_links_checked13093 : (cuts13093.take 2).map (fun c => (1720057857-1+2*2^9*c.k,94478746145441+c.lower,94479122938675+c.upper)) = pointBounds13093 := by
 decide +kernel
def cuts13094 : List PrefixCut := [⟨21,167719936,167720056⟩,
⟨74,583983501,583983920⟩,
⟨127,1006778646,1006779366⟩,
⟨128,1014141447,1014142172⟩]
theorem checked13094 : checkPrefixCuts (2^48) 1720188929 9 Manual.Count131072.C013094.packed 128 cuts13094 = true := by
 decide +kernel
def pointBounds13094 : List (Nat × Nat × Nat) := [(1720210432,94479921211354,94480298005434),(1720264704,94480337474919,94480714269298),(1720318976,94480760270064,94481137064744)]
theorem point_links_checked13094 : (cuts13094.take 3).map (fun c => (1720188929-1+2*2^9*c.k,94479753491418+c.lower,94480130285378+c.upper)) = pointBounds13094 := by
 decide +kernel
def cuts13095 : List PrefixCut := [⟨52,405274937,405275235⟩,
⟨105,814136542,814137141⟩,
⟨128,995412433,995413160⟩]
theorem checked13095 : checkPrefixCuts (2^48) 1720320001 9 Manual.Count131072.C013095.packed 128 cuts13095 = true := by
 decide +kernel
def pointBounds13095 : List (Nat × Nat × Nat) := [(1720373248,94481172907802,94481549702785),(1720427520,94481581769407,94481958564691)]
theorem point_links_checked13095 : (cuts13095.take 2).map (fun c => (1720320001-1+2*2^9*c.k,94480767632865+c.lower,94481144427550+c.upper)) = pointBounds13095 := by
 decide +kernel
def cuts13096 : List PrefixCut := [⟨30,235916689,235916860⟩,
⟨83,657840568,657841049⟩,
⟨128,1013005316,1013006053⟩]
theorem checked13096 : checkPrefixCuts (2^48) 1720451073 9 Manual.Count131072.C013096.packed 128 cuts13096 = true := by
 decide +kernel
def pointBounds13096 : List (Nat × Nat × Nat) := [(1720481792,94481998961987,94482375757570),(1720536064,94482420885866,94482797681759)]
theorem point_links_checked13096 : (cuts13096.take 2).map (fun c => (1720451073-1+2*2^9*c.k,94481763045298+c.lower,94482139840710+c.upper)) = pointBounds13096 := by
 decide +kernel
def cuts13097 : List PrefixCut := [⟨8,60202012,60202055⟩,
⟨61,478009446,478009790⟩,
⟨114,901692801,901693449⟩,
⟨128,1012927905,1012928633⟩]
theorem checked13097 : checkPrefixCuts (2^48) 1720582145 9 Manual.Count131072.C013097.packed 128 cuts13097 = true := by
 decide +kernel
def pointBounds13097 : List (Nat × Nat × Nat) := [(1720590336,94482836252626,94483213048818),(1720644608,94483254060060,94483630856553),(1720698880,94483677743415,94484054540212)]
theorem point_links_checked13097 : (cuts13097.take 3).map (fun c => (1720582145-1+2*2^9*c.k,94482776050614+c.lower,94483152846763+c.upper)) = pointBounds13097 := by
 decide +kernel
def cuts13098 : List PrefixCut := [⟨39,303765197,303765420⟩,
⟨92,709265178,709265696⟩,
⟨128,991422811,991423533⟩]
theorem checked13098 : checkPrefixCuts (2^48) 1720713217 9 Manual.Count131072.C013098.packed 128 cuts13098 = true := by
 decide +kernel
def pointBounds13098 : List (Nat × Nat × Nat) := [(1720753152,94484092743716,94484469540816),(1720807424,94484498243697,94484875041092)]
theorem point_links_checked13098 : (cuts13098.take 2).map (fun c => (1720713217-1+2*2^9*c.k,94483788978519+c.lower,94484165775396+c.upper)) = pointBounds13098 := by
 decide +kernel
def cuts13099 : List PrefixCut := [⟨17,140994818,140994920⟩,
⟨70,566751067,566751474⟩,
⟨123,985297249,985297957⟩,
⟨128,1024714167,1024714904⟩]
theorem checked13099 : checkPrefixCuts (2^48) 1720844289 9 Manual.Count131072.C013099.packed 128 cuts13099 = true := by
 decide +kernel
def pointBounds13099 : List (Nat × Nat × Nat) := [(1720861696,94484921396148,94485298193849),(1720915968,94485347152397,94485723950403),(1720970240,94485765698579,94486142496886)]
theorem point_links_checked13099 : (cuts13099.take 3).map (fun c => (1720844289-1+2*2^9*c.k,94484780401330+c.lower,94485157198929+c.upper)) = pointBounds13099 := by
 decide +kernel
def cuts13100 : List PrefixCut := [⟨48,376662778,376663050⟩,
⟨101,805976742,805977325⟩,
⟨128,1014659249,1014659984⟩]
theorem checked13100 : checkPrefixCuts (2^48) 1720975361 9 Manual.Count131072.C013100.packed 128 cuts13100 = true := by
 decide +kernel
def pointBounds13100 : List (Nat × Nat × Nat) := [(1721024512,94486181778275,94486558576883),(1721078784,94486611092239,94486987891158)]
theorem point_links_checked13100 : (cuts13100.take 2).map (fun c => (1720975361-1+2*2^9*c.k,94485805115497+c.lower,94486181913833+c.upper)) = pointBounds13100 := by
 decide +kernel
def cuts13101 : List PrefixCut := [⟨26,202301079,202301228⟩,
⟨79,623901757,623902208⟩,
⟨128,1008858290,1008859020⟩]
theorem checked13101 : checkPrefixCuts (2^48) 1721106433 9 Manual.Count131072.C013101.packed 128 cuts13101 = true := by
 decide +kernel
def pointBounds13101 : List (Nat × Nat × Nat) := [(1721133056,94487022075825,94487398875045),(1721187328,94487443676503,94487820476025)]
theorem point_links_checked13101 : (cuts13101.take 2).map (fun c => (1721106433-1+2*2^9*c.k,94486819774746+c.lower,94487196573817+c.upper)) = pointBounds13101 := by
 decide +kernel
def cuts13102 : List PrefixCut := [⟨4,33196659,33196684⟩,
⟨57,447411936,447412257⟩,
⟨110,857853134,857853754⟩,
⟨128,996844251,996844969⟩]
theorem checked13102 : checkPrefixCuts (2^48) 1721237505 9 Manual.Count131072.C013102.packed 128 cuts13102 = true := by
 decide +kernel
def pointBounds13102 : List (Nat × Nat × Nat) := [(1721241600,94487861829695,94488238629521),(1721295872,94488276044972,94488652845094),(1721350144,94488686486170,94489063286591)]
theorem point_links_checked13102 : (cuts13102.take 3).map (fun c => (1721237505-1+2*2^9*c.k,94487828633036+c.lower,94488205432837+c.upper)) = pointBounds13102 := by
 decide +kernel
def cuts13103 : List PrefixCut := [⟨35,272418288,272418486⟩,
⟨88,693134917,693135415⟩,
⟨128,1012628726,1012629454⟩]
theorem checked13103 : checkPrefixCuts (2^48) 1721368577 9 Manual.Count131072.C013103.packed 128 cuts13103 = true := by
 decide +kernel
def pointBounds13103 : List (Nat × Nat × Nat) := [(1721404416,94489097895575,94489474696292),(1721458688,94489518612204,94489895413221)]
theorem point_links_checked13103 : (cuts13103.take 2).map (fun c => (1721368577-1+2*2^9*c.k,94488825477287+c.lower,94489202277806+c.upper)) = pointBounds13103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000096
