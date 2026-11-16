import PlattAssemblyKernel
import PlattCertificates.Count131072.C016080
import PlattCertificates.Count131072.C016081
import PlattCertificates.Count131072.C016082
import PlattCertificates.Count131072.C016083
import PlattCertificates.Count131072.C016084
import PlattCertificates.Count131072.C016085
import PlattCertificates.Count131072.C016086
import PlattCertificates.Count131072.C016087
import PlattCertificates.Count131072.C016088
import PlattCertificates.Count131072.C016089
import PlattCertificates.Count131072.C016090
import PlattCertificates.Count131072.C016091
import PlattCertificates.Count131072.C016092
import PlattCertificates.Count131072.C016093
import PlattCertificates.Count131072.C016094
import PlattCertificates.Count131072.C016095
import PlattCertificates.Count131072.C016096
import PlattCertificates.Count131072.C016097
import PlattCertificates.Count131072.C016098
import PlattCertificates.Count131072.C016099
import PlattCertificates.Count131072.C016100
import PlattCertificates.Count131072.C016101
import PlattCertificates.Count131072.C016102
import PlattCertificates.Count131072.C016103
import PlattCertificates.Count131072.C016104
import PlattCertificates.Count131072.C016105
import PlattCertificates.Count131072.C016106
import PlattCertificates.Count131072.C016107
import PlattCertificates.Count131072.C016108
import PlattCertificates.Count131072.C016109
import PlattCertificates.Count131072.C016110
import PlattCertificates.Count131072.C016111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16080 : List PrefixCut := [⟨63,405762768,405763032⟩,
⟨128,820177213,820177740⟩]
theorem checked16080 : checkPrefixCuts (2^48) 2111569921 9 Manual.Count131072.C016080.packed 128 cuts16080 = true := by
 decide +kernel
def pointBounds16080 : List (Nat × Nat × Nat) := [(2111634432,97180461631577,97180840261781),(2111700992,97180876046022,97181254676489)]
theorem point_links_checked16080 : (cuts16080.take 2).map (fun c => (2111569921-1+2*2^9*c.k,97180055868809+c.lower,97180434498749+c.upper)) = pointBounds16080 := by
 decide +kernel
def cuts16081 : List PrefixCut := [⟨65,415334293,415334559⟩,
⟨128,809863025,809863549⟩]
theorem checked16081 : checkPrefixCuts (2^48) 2111700993 9 Manual.Count131072.C016081.packed 128 cuts16081 = true := by
 decide +kernel
def pointBounds16081 : List (Nat × Nat × Nat) := [(2111767552,97181291380315,97181670011048)]
theorem point_links_checked16081 : (cuts16081.take 1).map (fun c => (2111700993-1+2*2^9*c.k,97180876046022+c.lower,97181254676489+c.upper)) = pointBounds16081 := by
 decide +kernel
def cuts16082 : List PrefixCut := [⟨2,14661309,14661318⟩,
⟨67,438099708,438099989⟩,
⟨128,830071468,830072000⟩]
theorem checked16082 : checkPrefixCuts (2^48) 2111832065 9 Manual.Count131072.C016082.packed 128 cuts16082 = true := by
 decide +kernel
def pointBounds16082 : List (Nat × Nat × Nat) := [(2111834112,97181700570356,97182079201356),(2111900672,97182124008755,97182502640027)]
theorem point_links_checked16082 : (cuts16082.take 2).map (fun c => (2111832065-1+2*2^9*c.k,97181685909047+c.lower,97182064540038+c.upper)) = pointBounds16082 := by
 decide +kernel
def cuts16083 : List PrefixCut := [⟨4,26521983,26521999⟩,
⟨69,440071282,440071559⟩,
⟨128,810695305,810695819⟩]
theorem checked16083 : checkPrefixCuts (2^48) 2111963137 9 Manual.Count131072.C016083.packed 128 cuts16083 = true := by
 decide +kernel
def pointBounds16083 : List (Nat × Nat × Nat) := [(2111967232,97182542502498,97182921134037),(2112033792,97182956051797,97183334683597)]
theorem point_links_checked16083 : (cuts16083.take 2).map (fun c => (2111963137-1+2*2^9*c.k,97182515980515+c.lower,97182894612038+c.upper)) = pointBounds16083 := by
 decide +kernel
def cuts16084 : List PrefixCut := [⟨6,35582541,35582564⟩,
⟨71,457235153,457235444⟩,
⟨128,818374448,818374970⟩]
theorem checked16084 : checkPrefixCuts (2^48) 2112094209 9 Manual.Count131072.C016084.packed 128 cuts16084 = true := by
 decide +kernel
def pointBounds16084 : List (Nat × Nat × Nat) := [(2112100352,97183362258361,97183740890421),(2112166912,97183783910973,97184162543301)]
theorem point_links_checked16084 : (cuts16084.take 2).map (fun c => (2112094209-1+2*2^9*c.k,97183326675820+c.lower,97183705307857+c.upper)) = pointBounds16084 := by
 decide +kernel
def cuts16085 : List PrefixCut := [⟨8,50505397,50505429⟩,
⟨73,456140508,456140801⟩,
⟨128,803532044,803532560⟩]
theorem checked16085 : checkPrefixCuts (2^48) 2112225281 9 Manual.Count131072.C016085.packed 128 cuts16085 = true := by
 decide +kernel
def pointBounds16085 : List (Nat × Nat × Nat) := [(2112233472,97184195555665,97184574188256),(2112300032,97184601190776,97184979823628)]
theorem point_links_checked16085 : (cuts16085.take 2).map (fun c => (2112225281-1+2*2^9*c.k,97184145050268+c.lower,97184523682827+c.upper)) = pointBounds16085 := by
 decide +kernel
def cuts16086 : List PrefixCut := [⟨10,65159881,65159922⟩,
⟨75,477298646,477298948⟩,
⟨128,811876961,811877472⟩]
theorem checked16086 : checkPrefixCuts (2^48) 2112356353 9 Manual.Count131072.C016086.packed 128 cuts16086 = true := by
 decide +kernel
def pointBounds16086 : List (Nat × Nat × Nat) := [(2112366592,97185013742193,97185392375309),(2112433152,97185425880958,97185804514335)]
theorem point_links_checked16086 : (cuts16086.take 2).map (fun c => (2112356353-1+2*2^9*c.k,97184948582312+c.lower,97185327215387+c.upper)) = pointBounds16086 := by
 decide +kernel
def cuts16087 : List PrefixCut := [⟨12,75948482,75948530⟩,
⟨77,481799031,481799335⟩,
⟨128,814357902,814358419⟩]
theorem checked16087 : checkPrefixCuts (2^48) 2112487425 9 Manual.Count131072.C016087.packed 128 cuts16087 = true := by
 decide +kernel
def pointBounds16087 : List (Nat × Nat × Nat) := [(2112499712,97185836407755,97186215041389),(2112566272,97186242258304,97186620892194)]
theorem point_links_checked16087 : (cuts16087.take 2).map (fun c => (2112487425-1+2*2^9*c.k,97185760459273+c.lower,97186139092859+c.upper)) = pointBounds16087 := by
 decide +kernel
def cuts16088 : List PrefixCut := [⟨14,89800139,89800197⟩,
⟨79,502553189,502553508⟩,
⟨128,814307657,814308174⟩]
theorem checked16088 : checkPrefixCuts (2^48) 2112618497 9 Manual.Count131072.C016088.packed 128 cuts16088 = true := by
 decide +kernel
def pointBounds16088 : List (Nat × Nat × Nat) := [(2112632832,97186664617314,97187043251475),(2112699392,97187077370364,97187456004786)]
theorem point_links_checked16088 : (cuts16088.take 2).map (fun c => (2112618497-1+2*2^9*c.k,97186574817175+c.lower,97186953451278+c.upper)) = pointBounds16088 := by
 decide +kernel
def cuts16089 : List PrefixCut := [⟨16,101651658,101651723⟩,
⟨81,508516774,508517099⟩,
⟨128,811725593,811726113⟩]
theorem checked16089 : checkPrefixCuts (2^48) 2112749569 9 Manual.Count131072.C016089.packed 128 cuts16089 = true := by
 decide +kernel
def pointBounds16089 : List (Nat × Nat × Nat) := [(2112765952,97187490776490,97187869411175),(2112832512,97187897641606,97188276276551)]
theorem point_links_checked16089 : (cuts16089.take 2).map (fun c => (2112749569-1+2*2^9*c.k,97187389124832+c.lower,97187767759452+c.upper)) = pointBounds16089 := by
 decide +kernel
def cuts16090 : List PrefixCut := [⟨18,116166062,116166139⟩,
⟨83,531797750,531798088⟩,
⟨128,811409194,811409715⟩]
theorem checked16090 : checkPrefixCuts (2^48) 2112880641 9 Manual.Count131072.C016090.packed 128 cuts16090 = true := by
 decide +kernel
def pointBounds16090 : List (Nat × Nat × Nat) := [(2112899072,97188317016487,97188695651704),(2112965632,97188732648175,97189111283653)]
theorem point_links_checked16090 : (cuts16090.take 2).map (fun c => (2112880641-1+2*2^9*c.k,97188200850425+c.lower,97188579485565+c.upper)) = pointBounds16090 := by
 decide +kernel
def cuts16091 : List PrefixCut := [⟨20,130545429,130545512⟩,
⟨85,541755075,541755425⟩,
⟨128,819351005,819351535⟩]
theorem checked16091 : checkPrefixCuts (2^48) 2113011713 9 Manual.Count131072.C016091.packed 128 cuts16091 = true := by
 decide +kernel
def pointBounds16091 : List (Nat × Nat × Nat) := [(2113032192,97189142805048,97189521440792),(2113098752,97189554014694,97189932650705)]
theorem point_links_checked16091 : (cuts16091.take 2).map (fun c => (2113011713-1+2*2^9*c.k,97189012259619+c.lower,97189390895280+c.upper)) = pointBounds16091 := by
 decide +kernel
def cuts16092 : List PrefixCut := [⟨22,144123807,144123897⟩,
⟨87,563832304,563832662⟩,
⟨128,820499267,820499790⟩]
theorem checked16092 : checkPrefixCuts (2^48) 2113142785 9 Manual.Count131072.C016092.packed 128 cuts16092 = true := by
 decide +kernel
def pointBounds16092 : List (Nat × Nat × Nat) := [(2113165312,97189975734431,97190354370712),(2113231872,97190395442928,97190774079477)]
theorem point_links_checked16092 : (cuts16092.take 2).map (fun c => (2113142785-1+2*2^9*c.k,97189831610624+c.lower,97190210246815+c.upper)) = pointBounds16092 := by
 decide +kernel
def cuts16093 : List PrefixCut := [⟨24,145047153,145047249⟩,
⟨89,562198559,562198918⟩,
⟨128,812190100,812190619⟩]
theorem checked16093 : checkPrefixCuts (2^48) 2113273857 9 Manual.Count131072.C016093.packed 128 cuts16093 = true := by
 decide +kernel
def pointBounds16093 : List (Nat × Nat × Nat) := [(2113298432,97190797157044,97191175793854),(2113364992,97191214308450,97191592945523)]
theorem point_links_checked16093 : (cuts16093.take 2).map (fun c => (2113273857-1+2*2^9*c.k,97190652109891+c.lower,97191030746605+c.upper)) = pointBounds16093 := by
 decide +kernel
def cuts16094 : List PrefixCut := [⟨26,159155675,159155777⟩,
⟨91,572951296,572951658⟩,
⟨128,816135100,816135620⟩]
theorem checked16094 : checkPrefixCuts (2^48) 2113404929 9 Manual.Count131072.C016094.packed 128 cuts16094 = true := by
 decide +kernel
def pointBounds16094 : List (Nat × Nat × Nat) := [(2113431552,97191623455666,97192002093001),(2113498112,97192037251287,97192415888882)]
theorem point_links_checked16094 : (cuts16094.take 2).map (fun c => (2113404929-1+2*2^9*c.k,97191464299991+c.lower,97191842937224+c.upper)) = pointBounds16094 := by
 decide +kernel
def cuts16095 : List PrefixCut := [⟨28,174194640,174194751⟩,
⟨93,586366136,586366514⟩,
⟨128,813154849,813155374⟩]
theorem checked16095 : checkPrefixCuts (2^48) 2113536001 9 Manual.Count131072.C016095.packed 128 cuts16095 = true := by
 decide +kernel
def pointBounds16095 : List (Nat × Nat × Nat) := [(2113564672,97192454629731,97192833267595),(2113631232,97192866801227,97193245439358)]
theorem point_links_checked16095 : (cuts16095.take 2).map (fun c => (2113536001-1+2*2^9*c.k,97192280435091+c.lower,97192659072844+c.upper)) = pointBounds16095 := by
 decide +kernel
def cuts16096 : List PrefixCut := [⟨30,188432751,188432876⟩,
⟨95,598980282,598980671⟩,
⟨128,803916287,803916808⟩]
theorem checked16096 : checkPrefixCuts (2^48) 2113667073 9 Manual.Count131072.C016096.packed 128 cuts16096 = true := by
 decide +kernel
def pointBounds16096 : List (Nat × Nat × Nat) := [(2113697792,97193282022691,97193660661094),(2113764352,97193692570222,97194071208889)]
theorem point_links_checked16096 : (cuts16096.take 2).map (fun c => (2113667073-1+2*2^9*c.k,97193093589940+c.lower,97193472228218+c.upper)) = pointBounds16096 := by
 decide +kernel
def cuts16097 : List PrefixCut := [⟨32,208128600,208128733⟩,
⟨97,620514413,620514816⟩,
⟨128,822641371,822641899⟩]
theorem checked16097 : checkPrefixCuts (2^48) 2113798145 9 Manual.Count131072.C016097.packed 128 cuts16097 = true := by
 decide +kernel
def pointBounds16097 : List (Nat × Nat × Nat) := [(2113830912,97194105634827,97194484273759),(2113897472,97194518020640,97194896659842)]
theorem point_links_checked16097 : (cuts16097.take 2).map (fun c => (2113798145-1+2*2^9*c.k,97193897506227+c.lower,97194276145026+c.upper)) = pointBounds16097 := by
 decide +kernel
def cuts16098 : List PrefixCut := [⟨34,209047670,209047804⟩,
⟨99,626733544,626733948⟩,
⟨128,812337884,812338408⟩]
theorem checked16098 : checkPrefixCuts (2^48) 2113929217 9 Manual.Count131072.C016098.packed 128 cuts16098 = true := by
 decide +kernel
def pointBounds16098 : List (Nat × Nat × Nat) := [(2113964032,97194929195268,97195307834729),(2114030592,97195346881142,97195725520873)]
theorem point_links_checked16098 : (cuts16098.take 2).map (fun c => (2113929217-1+2*2^9*c.k,97194720147598+c.lower,97195098786925+c.upper)) = pointBounds16098 := by
 decide +kernel
def cuts16099 : List PrefixCut := [⟨36,226076946,226077095⟩,
⟨101,640541131,640541540⟩,
⟨128,812820200,812820723⟩]
theorem checked16099 : checkPrefixCuts (2^48) 2114060289 9 Manual.Count131072.C016099.packed 128 cuts16099 = true := by
 decide +kernel
def pointBounds16099 : List (Nat × Nat × Nat) := [(2114097152,97195758562428,97196137202428),(2114163712,97196173026613,97196551666873)]
theorem point_links_checked16099 : (cuts16099.take 2).map (fun c => (2114060289-1+2*2^9*c.k,97195532485482+c.lower,97195911125333+c.upper)) = pointBounds16099 := by
 decide +kernel
def cuts16100 : List PrefixCut := [⟨38,241373285,241373441⟩,
⟨103,667260729,667261159⟩,
⟨128,827414323,827414855⟩]
theorem checked16100 : checkPrefixCuts (2^48) 2114191361 9 Manual.Count131072.C016100.packed 128 cuts16100 = true := by
 decide +kernel
def pointBounds16100 : List (Nat × Nat × Nat) := [(2114230272,97196586678967,97196965319497),(2114296832,97197012566411,97197391207215)]
theorem point_links_checked16100 : (cuts16100.take 2).map (fun c => (2114191361-1+2*2^9*c.k,97196345305682+c.lower,97196723946056+c.upper)) = pointBounds16100 := by
 decide +kernel
def cuts16101 : List PrefixCut := [⟨40,259064037,259064202⟩,
⟨105,673875437,673875869⟩,
⟨128,819775167,819775695⟩]
theorem checked16101 : checkPrefixCuts (2^48) 2114322433 9 Manual.Count131072.C016101.packed 128 cuts16101 = true := by
 decide +kernel
def pointBounds16101 : List (Nat × Nat × Nat) := [(2114363392,97197431784042,97197810425113),(2114429952,97197846595442,97198225236780)]
theorem point_links_checked16101 : (cuts16101.take 2).map (fun c => (2114322433-1+2*2^9*c.k,97197172720005+c.lower,97197551360911+c.upper)) = pointBounds16101 := by
 decide +kernel
def cuts16102 : List PrefixCut := [⟨42,277418085,277418261⟩,
⟨107,689940325,689940773⟩,
⟨128,823451531,823452065⟩]
theorem checked16102 : checkPrefixCuts (2^48) 2114453505 9 Manual.Count131072.C016102.packed 128 cuts16102 = true := by
 decide +kernel
def pointBounds16102 : List (Nat × Nat × Nat) := [(2114496512,97198269913257,97198648554867),(2114563072,97198682435497,97199061077379)]
theorem point_links_checked16102 : (cuts16102.take 2).map (fun c => (2114453505-1+2*2^9*c.k,97197992495172+c.lower,97198371136606+c.upper)) = pointBounds16102 := by
 decide +kernel
def cuts16103 : List PrefixCut := [⟨44,286319163,286319346⟩,
⟨109,688300040,688300478⟩,
⟨128,806496007,806496524⟩]
theorem checked16103 : checkPrefixCuts (2^48) 2114584577 9 Manual.Count131072.C016103.packed 128 cuts16103 = true := by
 decide +kernel
def pointBounds16103 : List (Nat × Nat × Nat) := [(2114629632,97199102265866,97199480908017),(2114696192,97199504246743,97199882889149)]
theorem point_links_checked16103 : (cuts16103.take 2).map (fun c => (2114584577-1+2*2^9*c.k,97198815946703+c.lower,97199194588671+c.upper)) = pointBounds16103 := by
 decide +kernel
def cuts16104 : List PrefixCut := [⟨46,295485273,295485461⟩,
⟨111,705027605,705028060⟩,
⟨128,811237608,811238131⟩]
theorem checked16104 : checkPrefixCuts (2^48) 2114715649 9 Manual.Count131072.C016104.packed 128 cuts16104 = true := by
 decide +kernel
def pointBounds16104 : List (Nat × Nat × Nat) := [(2114762752,97199917927983,97200296570656),(2114829312,97200327470315,97200706113255)]
theorem point_links_checked16104 : (cuts16104.take 2).map (fun c => (2114715649-1+2*2^9*c.k,97199622442710+c.lower,97200001085195+c.upper)) = pointBounds16104 := by
 decide +kernel
def cuts16105 : List PrefixCut := [⟨48,301322877,301323068⟩,
⟨113,710173964,710174416⟩,
⟨128,805064943,805065457⟩]
theorem checked16105 : checkPrefixCuts (2^48) 2114846721 9 Manual.Count131072.C016105.packed 128 cuts16105 = true := by
 decide +kernel
def pointBounds16105 : List (Nat × Nat × Nat) := [(2114895872,97200735003195,97201113646394),(2114962432,97201143854282,97201522497742)]
theorem point_links_checked16105 : (cuts16105.take 2).map (fun c => (2114846721-1+2*2^9*c.k,97200433680318+c.lower,97200812323326+c.upper)) = pointBounds16105 := by
 decide +kernel
def cuts16106 : List PrefixCut := [⟨50,319669700,319669904⟩,
⟨115,731555862,731556324⟩,
⟨128,815262316,815262833⟩]
theorem checked16106 : checkPrefixCuts (2^48) 2114977793 9 Manual.Count131072.C016106.packed 128 cuts16106 = true := by
 decide +kernel
def pointBounds16106 : List (Nat × Nat × Nat) := [(2115028992,97201558414961,97201937058687),(2115095552,97201970301123,97202348945107)]
theorem point_links_checked16106 : (cuts16106.take 2).map (fun c => (2114977793-1+2*2^9*c.k,97201238745261+c.lower,97201617388783+c.upper)) = pointBounds16106 := by
 decide +kernel
def cuts16107 : List PrefixCut := [⟨52,329231368,329231575⟩,
⟨117,740426158,740426628⟩,
⟨128,806429030,806429544⟩]
theorem checked16107 : checkPrefixCuts (2^48) 2115108865 9 Manual.Count131072.C016107.packed 128 cuts16107 = true := by
 decide +kernel
def pointBounds16107 : List (Nat × Nat × Nat) := [(2115162112,97202383238945,97202761883191),(2115228672,97202794433735,97203173078244)]
theorem point_links_checked16107 : (cuts16107.take 2).map (fun c => (2115108865-1+2*2^9*c.k,97202054007577+c.lower,97202432651616+c.upper)) = pointBounds16107 := by
 decide +kernel
def cuts16108 : List PrefixCut := [⟨54,341852269,341852483⟩,
⟨119,753686534,753687011⟩,
⟨128,810370948,810371462⟩]
theorem checked16108 : checkPrefixCuts (2^48) 2115239937 9 Manual.Count131072.C016108.packed 128 cuts16108 = true := by
 decide +kernel
def pointBounds16108 : List (Nat × Nat × Nat) := [(2115295232,97203202288876,97203580933643),(2115361792,97203614123141,97203992768171)]
theorem point_links_checked16108 : (cuts16108.take 2).map (fun c => (2115239937-1+2*2^9*c.k,97202860436607+c.lower,97203239081160+c.upper)) = pointBounds16108 := by
 decide +kernel
def cuts16109 : List PrefixCut := [⟨56,354471612,354471843⟩,
⟨121,761889173,761889666⟩,
⟨128,806462159,806462681⟩]
theorem checked16109 : checkPrefixCuts (2^48) 2115371009 9 Manual.Count131072.C016109.packed 128 cuts16109 = true := by
 decide +kernel
def pointBounds16109 : List (Nat × Nat × Nat) := [(2115428352,97204025279167,97204403924465),(2115494912,97204432696728,97204811342288)]
theorem point_links_checked16109 : (cuts16109.take 2).map (fun c => (2115371009-1+2*2^9*c.k,97203670807555+c.lower,97204049452622+c.upper)) = pointBounds16109 := by
 decide +kernel
def cuts16110 : List PrefixCut := [⟨58,368952073,368952311⟩,
⟨123,776743126,776743624⟩,
⟨128,807476609,807477126⟩]
theorem checked16110 : checkPrefixCuts (2^48) 2115502081 9 Manual.Count131072.C016110.packed 128 cuts16110 = true := by
 decide +kernel
def pointBounds16110 : List (Nat × Nat × Nat) := [(2115561472,97204846221787,97205224867614),(2115628032,97205254012840,97205632658927)]
theorem point_links_checked16110 : (cuts16110.take 2).map (fun c => (2115502081-1+2*2^9*c.k,97204477269714+c.lower,97204855915303+c.upper)) = pointBounds16110 := by
 decide +kernel
def cuts16111 : List PrefixCut := [⟨60,389816913,389817163⟩,
⟨125,793724102,793724610⟩,
⟨128,814078774,814079295⟩]
theorem checked16111 : checkPrefixCuts (2^48) 2115633153 9 Manual.Count131072.C016111.packed 128 cuts16111 = true := by
 decide +kernel
def pointBounds16111 : List (Nat × Nat × Nat) := [(2115694592,97205674563236,97206053209592),(2115761152,97206078470425,97206457117039)]
theorem point_links_checked16111 : (cuts16111.take 2).map (fun c => (2115633153-1+2*2^9*c.k,97205284746323+c.lower,97205663392429+c.upper)) = pointBounds16111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000190
