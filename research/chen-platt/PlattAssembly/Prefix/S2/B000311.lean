import PlattAssemblyKernel
import PlattCertificates.Count131072.C019952
import PlattCertificates.Count131072.C019953
import PlattCertificates.Count131072.C019954
import PlattCertificates.Count131072.C019955
import PlattCertificates.Count131072.C019956
import PlattCertificates.Count131072.C019957
import PlattCertificates.Count131072.C019958
import PlattCertificates.Count131072.C019959
import PlattCertificates.Count131072.C019960
import PlattCertificates.Count131072.C019961
import PlattCertificates.Count131072.C019962
import PlattCertificates.Count131072.C019963
import PlattCertificates.Count131072.C019964
import PlattCertificates.Count131072.C019965
import PlattCertificates.Count131072.C019966
import PlattCertificates.Count131072.C019967
import PlattCertificates.Count131072.C019968
import PlattCertificates.Count131072.C019969
import PlattCertificates.Count131072.C019970
import PlattCertificates.Count131072.C019971
import PlattCertificates.Count131072.C019972
import PlattCertificates.Count131072.C019973
import PlattCertificates.Count131072.C019974
import PlattCertificates.Count131072.C019975
import PlattCertificates.Count131072.C019976
import PlattCertificates.Count131072.C019977
import PlattCertificates.Count131072.C019978
import PlattCertificates.Count131072.C019979
import PlattCertificates.Count131072.C019980
import PlattCertificates.Count131072.C019981
import PlattCertificates.Count131072.C019982
import PlattCertificates.Count131072.C019983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000311
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19952 : List PrefixCut := [⟨29,144440030,144440117⟩,
⟨109,553678126,553678454⟩,
⟨128,652869149,652869533⟩]
theorem checked19952 : checkPrefixCuts (2^48) 2619080705 9 Manual.Count131072.C019952.packed 128 cuts19952 = true := by
 decide +kernel
def pointBounds19952 : List (Nat × Nat × Nat) := [(2619110400,99989871026961,99990251378511),(2619192320,99990280265057,99990660616848)]
theorem point_links_checked19952 : (cuts19952.take 2).map (fun c => (2619080705-1+2*2^9*c.k,99989726586931+c.lower,99990106938394+c.upper)) = pointBounds19952 := by
 decide +kernel
def cuts19953 : List PrefixCut := [⟨61,307347674,307347852⟩,
⟨128,645099236,645099615⟩]
theorem checked19953 : checkPrefixCuts (2^48) 2619211777 9 Manual.Count131072.C019953.packed 128 cuts19953 = true := by
 decide +kernel
def pointBounds19953 : List (Nat × Nat × Nat) := [(2619274240,99990686803754,99991067155779)]
theorem point_links_checked19953 : (cuts19953.take 1).map (fun c => (2619211777-1+2*2^9*c.k,99990379456080+c.lower,99990759807927+c.upper)) = pointBounds19953 := by
 decide +kernel
def cuts19954 : List PrefixCut := [⟨13,61789407,61789446⟩,
⟨93,469914449,469914725⟩,
⟨128,648290550,648290930⟩]
theorem checked19954 : checkPrefixCuts (2^48) 2619342849 9 Manual.Count131072.C019954.packed 128 cuts19954 = true := by
 decide +kernel
def pointBounds19954 : List (Nat × Nat × Nat) := [(2619356160,99991086344723,99991466696988),(2619438080,99991494469765,99991874822267)]
theorem point_links_checked19954 : (cuts19954.take 2).map (fun c => (2619342849-1+2*2^9*c.k,99991024555316+c.lower,99991404907542+c.upper)) = pointBounds19954 := by
 decide +kernel
def cuts19955 : List PrefixCut := [⟨45,228554231,228554362⟩,
⟨125,633215323,633215689⟩,
⟨128,648258243,648258618⟩]
theorem checked19955 : checkPrefixCuts (2^48) 2619473921 9 Manual.Count131072.C019955.packed 128 cuts19955 = true := by
 decide +kernel
def pointBounds19955 : List (Nat × Nat × Nat) := [(2619520000,99991901400097,99992281752834),(2619601920,99992306061189,99992686414161)]
theorem point_links_checked19955 : (cuts19955.take 2).map (fun c => (2619473921-1+2*2^9*c.k,99991672845866+c.lower,99992053198472+c.upper)) = pointBounds19955 := by
 decide +kernel
def cuts19956 : List PrefixCut := [⟨77,396589660,396589896⟩,
⟨128,658863041,658863430⟩]
theorem checked19956 : checkPrefixCuts (2^48) 2619604993 9 Manual.Count131072.C019956.packed 128 cuts19956 = true := by
 decide +kernel
def pointBounds19956 : List (Nat × Nat × Nat) := [(2619683840,99992717693769,99993098046986)]
theorem point_links_checked19956 : (cuts19956.take 1).map (fun c => (2619604993-1+2*2^9*c.k,99992321104109+c.lower,99992701457090+c.upper)) = pointBounds19956 := by
 decide +kernel
def cuts19957 : List PrefixCut := [⟨29,144833686,144833772⟩,
⟨109,561060506,561060837⟩,
⟨128,653565495,653565881⟩]
theorem checked19957 : checkPrefixCuts (2^48) 2619736065 9 Manual.Count131072.C019957.packed 128 cuts19957 = true := by
 decide +kernel
def pointBounds19957 : List (Nat × Nat × Nat) := [(2619765760,99993124800836,99993505154292),(2619847680,99993541027656,99993921381357)]
theorem point_links_checked19957 : (cuts19957.take 2).map (fun c => (2619736065-1+2*2^9*c.k,99992979967150+c.lower,99993360320520+c.upper)) = pointBounds19957 := by
 decide +kernel
def cuts19958 : List PrefixCut := [⟨61,304262511,304262696⟩,
⟨128,641499908,641500294⟩]
theorem checked19958 : checkPrefixCuts (2^48) 2619867137 9 Manual.Count131072.C019958.packed 128 cuts19958 = true := by
 decide +kernel
def pointBounds19958 : List (Nat × Nat × Nat) := [(2619929600,99993937795156,99994318149097)]
theorem point_links_checked19958 : (cuts19958.take 1).map (fun c => (2619867137-1+2*2^9*c.k,99993633532645+c.lower,99994013886401+c.upper)) = pointBounds19958 := by
 decide +kernel
def cuts19959 : List PrefixCut := [⟨13,66501001,66501041⟩,
⟨93,472375361,472375639⟩,
⟨128,649202825,649203202⟩]
theorem checked19959 : checkPrefixCuts (2^48) 2619998209 9 Manual.Count131072.C019959.packed 128 cuts19959 = true := by
 decide +kernel
def pointBounds19959 : List (Nat × Nat × Nat) := [(2620011520,99994341533554,99994721887736),(2620093440,99994747407914,99995127762334)]
theorem point_links_checked19959 : (cuts19959.take 2).map (fun c => (2619998209-1+2*2^9*c.k,99994275032553+c.lower,99994655386695+c.upper)) = pointBounds19959 := by
 decide +kernel
def cuts19960 : List PrefixCut := [⟨45,229893601,229893734⟩,
⟨125,634561023,634561390⟩,
⟨128,649815026,649815402⟩]
theorem checked19960 : checkPrefixCuts (2^48) 2620129281 9 Manual.Count131072.C019960.packed 128 cuts19960 = true := by
 decide +kernel
def pointBounds19960 : List (Nat × Nat × Nat) := [(2620175360,99995154128979,99995534483631),(2620257280,99995558796401,99995939151287)]
theorem point_links_checked19960 : (cuts19960.take 2).map (fun c => (2620129281-1+2*2^9*c.k,99994924235378+c.lower,99995304589897+c.upper)) = pointBounds19960 := by
 decide +kernel
def cuts19961 : List PrefixCut := [⟨77,398101721,398101952⟩,
⟨128,663424639,663425029⟩]
theorem checked19961 : checkPrefixCuts (2^48) 2620260353 9 Manual.Count131072.C019961.packed 128 cuts19961 = true := by
 decide +kernel
def pointBounds19961 : List (Nat × Nat × Nat) := [(2620339200,99995972152125,99996352507251)]
theorem point_links_checked19961 : (cuts19961.take 1).map (fun c => (2620260353-1+2*2^9*c.k,99995574050404+c.lower,99995954405299+c.upper)) = pointBounds19961 := by
 decide +kernel
def cuts19962 : List PrefixCut := [⟨29,142971365,142971447⟩,
⟨109,552649234,552649555⟩,
⟨128,646205216,646205593⟩]
theorem checked19962 : checkPrefixCuts (2^48) 2620391425 9 Manual.Count131072.C019962.packed 128 cuts19962 = true := by
 decide +kernel
def pointBounds19962 : List (Nat × Nat × Nat) := [(2620421120,99996380446408,99996760801775),(2620503040,99996790124277,99997170479883)]
theorem point_links_checked19962 : (cuts19962.take 2).map (fun c => (2620391425-1+2*2^9*c.k,99996237475043+c.lower,99996617830328+c.upper)) = pointBounds19962 := by
 decide +kernel
def cuts19963 : List PrefixCut := [⟨61,310308866,310309049⟩,
⟨128,650469246,650469630⟩]
theorem checked19963 : checkPrefixCuts (2^48) 2620522497 9 Manual.Count131072.C019963.packed 128 cuts19963 = true := by
 decide +kernel
def pointBounds19963 : List (Nat × Nat × Nat) := [(2620584960,99997193989125,99997574344970)]
theorem point_links_checked19963 : (cuts19963.take 1).map (fun c => (2620522497-1+2*2^9*c.k,99996883680259+c.lower,99997264035921+c.upper)) = pointBounds19963 := by
 decide +kernel
def cuts19964 : List PrefixCut := [⟨13,65410313,65410352⟩,
⟨93,468498144,468498420⟩,
⟨128,649792281,649792660⟩]
theorem checked19964 : checkPrefixCuts (2^48) 2620653569 9 Manual.Count131072.C019964.packed 128 cuts19964 = true := by
 decide +kernel
def pointBounds19964 : List (Nat × Nat × Nat) := [(2620666880,99997599559818,99997979915903),(2620748800,99998002647649,99998383003971)]
theorem point_links_checked19964 : (cuts19964.take 2).map (fun c => (2620653569-1+2*2^9*c.k,99997534149505+c.lower,99997914505551+c.upper)) = pointBounds19964 := by
 decide +kernel
def cuts19965 : List PrefixCut := [⟨45,225110510,225110641⟩,
⟨125,630643236,630643606⟩,
⟨128,645571237,645571615⟩]
theorem checked19965 : checkPrefixCuts (2^48) 2620784641 9 Manual.Count131072.C019965.packed 128 cuts19965 = true := by
 decide +kernel
def pointBounds19965 : List (Nat × Nat × Nat) := [(2620830720,99998409052296,99998789408852),(2620912640,99998814585022,99999194941817)]
theorem point_links_checked19965 : (cuts19965.take 2).map (fun c => (2620784641-1+2*2^9*c.k,99998183941786+c.lower,99998564298211+c.upper)) = pointBounds19965 := by
 decide +kernel
def cuts19966 : List PrefixCut := [⟨77,395102557,395102790⟩,
⟨128,650479141,650479522⟩]
theorem checked19966 : checkPrefixCuts (2^48) 2620915713 9 Manual.Count131072.C019966.packed 128 cuts19966 = true := by
 decide +kernel
def pointBounds19966 : List (Nat × Nat × Nat) := [(2620994560,99999224615580,99999604972616)]
theorem point_links_checked19966 : (cuts19966.take 1).map (fun c => (2620915713-1+2*2^9*c.k,99998829513023+c.lower,99999209869826+c.upper)) = pointBounds19966 := by
 decide +kernel
def cuts19967 : List PrefixCut := [⟨29,153781980,153782070⟩,
⟨109,563142625,563142956⟩,
⟨128,655386588,655386975⟩]
theorem checked19967 : checkPrefixCuts (2^48) 2621046785 9 Manual.Count131072.C019967.packed 128 cuts19967 = true := by
 decide +kernel
def pointBounds19967 : List (Nat × Nat × Nat) := [(2621076480,99999633774144,100000014131418),(2621158400,100000043134789,100000423492304)]
theorem point_links_checked19967 : (cuts19967.take 2).map (fun c => (2621046785-1+2*2^9*c.k,99999479992164+c.lower,99999860349348+c.upper)) = pointBounds19967 := by
 decide +kernel
def cuts19968 : List PrefixCut := [⟨61,312701086,312701267⟩,
⟨128,643756531,643756907⟩]
theorem checked19968 : checkPrefixCuts (2^48) 2621177857 9 Manual.Count131072.C019968.packed 128 cuts19968 = true := by
 decide +kernel
def pointBounds19968 : List (Nat × Nat × Nat) := [(2621240320,100000448079838,100000828437590)]
theorem point_links_checked19968 : (cuts19968.take 1).map (fun c => (2621177857-1+2*2^9*c.k,100000135378752+c.lower,100000515736323+c.upper)) = pointBounds19968 := by
 decide +kernel
def cuts19969 : List PrefixCut := [⟨13,69152235,69152275⟩,
⟨93,475145746,475146031⟩,
⟨128,652636412,652636802⟩]
theorem checked19969 : checkPrefixCuts (2^48) 2621308929 9 Manual.Count131072.C019969.packed 128 cuts19969 = true := by
 decide +kernel
def pointBounds19969 : List (Nat × Nat × Nat) := [(2621322240,100000848287518,100001228645505),(2621404160,100001254281029,100001634639261)]
theorem point_links_checked19969 : (cuts19969.take 2).map (fun c => (2621308929-1+2*2^9*c.k,100000779135283+c.lower,100001159493230+c.upper)) = pointBounds19969 := by
 decide +kernel
def cuts19970 : List PrefixCut := [⟨45,230530268,230530404⟩,
⟨126,640363722,640364097⟩,
⟨128,650778498,650778879⟩]
theorem checked19970 : checkPrefixCuts (2^48) 2621440001 9 Manual.Count131072.C019970.packed 128 cuts19970 = true := by
 decide +kernel
def pointBounds19970 : List (Nat × Nat × Nat) := [(2621486080,100001662301963,100002042660436),(2621569024,100002072135417,100002452494129)]
theorem point_links_checked19970 : (cuts19970.take 2).map (fun c => (2621440001-1+2*2^9*c.k,100001431771695+c.lower,100001812130032+c.upper)) = pointBounds19970 := by
 decide +kernel
def cuts19971 : List PrefixCut := [⟨79,401016234,401016471⟩,
⟨128,646343977,646344360⟩]
theorem checked19971 : checkPrefixCuts (2^48) 2621571073 9 Manual.Count131072.C019971.packed 128 cuts19971 = true := by
 decide +kernel
def pointBounds19971 : List (Nat × Nat × Nat) := [(2621651968,100002483566427,100002863925382)]
theorem point_links_checked19971 : (cuts19971.take 1).map (fun c => (2621571073-1+2*2^9*c.k,100002082550193+c.lower,100002462908911+c.upper)) = pointBounds19971 := by
 decide +kernel
def cuts19972 : List PrefixCut := [⟨32,164265005,164265103⟩,
⟨113,579749615,579749951⟩,
⟨128,657799141,657799523⟩]
theorem checked19972 : checkPrefixCuts (2^48) 2621702145 9 Manual.Count131072.C019972.packed 128 cuts19972 = true := by
 decide +kernel
def pointBounds19972 : List (Nat × Nat × Nat) := [(2621734912,100002893159175,100003273518374),(2621817856,100003308643785,100003689003222)]
theorem point_links_checked19972 : (cuts19972.take 2).map (fun c => (2621702145-1+2*2^9*c.k,100002728894170+c.lower,100003109253271+c.upper)) = pointBounds19972 := by
 decide +kernel
def cuts19973 : List PrefixCut := [⟨66,339998541,339998745⟩,
⟨128,649392712,649393095⟩]
theorem checked19973 : checkPrefixCuts (2^48) 2621833217 9 Manual.Count131072.C019973.packed 128 cuts19973 = true := by
 decide +kernel
def pointBounds19973 : List (Nat × Nat × Nat) := [(2621900800,100003726691852,100004107051539)]
theorem point_links_checked19973 : (cuts19973.take 1).map (fun c => (2621833217-1+2*2^9*c.k,100003386693311+c.lower,100003767052794+c.upper)) = pointBounds19973 := by
 decide +kernel
def cuts19974 : List PrefixCut := [⟨19,100911140,100911197⟩,
⟨100,508627145,508627444⟩,
⟨128,647427980,647428359⟩]
theorem checked19974 : checkPrefixCuts (2^48) 2621964289 9 Manual.Count131072.C019974.packed 128 cuts19974 = true := by
 decide +kernel
def pointBounds19974 : List (Nat × Nat × Nat) := [(2621983744,100004136997163,100004517357086),(2622066688,100004544713168,100004925073333)]
theorem point_links_checked19974 : (cuts19974.take 2).map (fun c => (2621964289-1+2*2^9*c.k,100004036086023+c.lower,100004416445889+c.upper)) = pointBounds19974 := by
 decide +kernel
def cuts19975 : List PrefixCut := [⟨53,268365510,268365665⟩,
⟨128,653406713,653407094⟩]
theorem checked19975 : checkPrefixCuts (2^48) 2622095361 9 Manual.Count131072.C019975.packed 128 cuts19975 = true := by
 decide +kernel
def pointBounds19975 : List (Nat × Nat × Nat) := [(2622149632,100004951879513,100005332239913)]
theorem point_links_checked19975 : (cuts19975.take 1).map (fun c => (2622095361-1+2*2^9*c.k,100004683514003+c.lower,100005063874248+c.upper)) = pointBounds19975 := by
 decide +kernel
def cuts19976 : List PrefixCut := [⟨6,29196976,29196993⟩,
⟨87,427750388,427750637⟩,
⟨128,635555672,635556044⟩]
theorem checked19976 : checkPrefixCuts (2^48) 2622226433 9 Manual.Count131072.C019976.packed 128 cuts19976 = true := by
 decide +kernel
def pointBounds19976 : List (Nat × Nat × Nat) := [(2622232576,100005366117692,100005746478335),(2622315520,100005764671104,100006145031979)]
theorem point_links_checked19976 : (cuts19976.take 2).map (fun c => (2622226433-1+2*2^9*c.k,100005336920716+c.lower,100005717281342+c.upper)) = pointBounds19976 := by
 decide +kernel
def cuts19977 : List PrefixCut := [⟨40,207265312,207265433⟩,
⟨121,616419594,616419956⟩,
⟨128,650443637,650444020⟩]
theorem checked19977 : checkPrefixCuts (2^48) 2622357505 9 Manual.Count131072.C019977.packed 128 cuts19977 = true := by
 decide +kernel
def pointBounds19977 : List (Nat × Nat × Nat) := [(2622398464,100006179741700,100006560102819),(2622481408,100006588895982,100006969257342)]
theorem point_links_checked19977 : (cuts19977.take 2).map (fun c => (2622357505-1+2*2^9*c.k,100005972476388+c.lower,100006352837386+c.upper)) = pointBounds19977 := by
 decide +kernel
def cuts19978 : List PrefixCut := [⟨74,377585768,377585993⟩,
⟨128,646761863,646762248⟩]
theorem checked19978 : checkPrefixCuts (2^48) 2622488577 9 Manual.Count131072.C019978.packed 128 cuts19978 = true := by
 decide +kernel
def pointBounds19978 : List (Nat × Nat × Nat) := [(2622564352,100007000505793,100007380867399)]
theorem point_links_checked19978 : (cuts19978.take 1).map (fun c => (2622488577-1+2*2^9*c.k,100006622920025+c.lower,100007003281406+c.upper)) = pointBounds19978 := by
 decide +kernel
def cuts19979 : List PrefixCut := [⟨27,141025426,141025509⟩,
⟨108,549711553,549711879⟩,
⟨128,649412678,649413060⟩]
theorem checked19979 : checkPrefixCuts (2^48) 2622619649 9 Manual.Count131072.C019979.packed 128 cuts19979 = true := by
 decide +kernel
def pointBounds19979 : List (Nat × Nat × Nat) := [(2622647296,100007410707314,100007791069163),(2622730240,100007819393441,100008199755533)]
theorem point_links_checked19979 : (cuts19979.take 2).map (fun c => (2622619649-1+2*2^9*c.k,100007269681888+c.lower,100007650043654+c.upper)) = pointBounds19979 := by
 decide +kernel
def cuts19980 : List PrefixCut := [⟨61,310474505,310474690⟩,
⟨128,649916730,649917116⟩]
theorem checked19980 : checkPrefixCuts (2^48) 2622750721 9 Manual.Count131072.C019980.packed 128 cuts19980 = true := by
 decide +kernel
def pointBounds19980 : List (Nat × Nat × Nat) := [(2622813184,100008229569071,100008609931404)]
theorem point_links_checked19980 : (cuts19980.take 1).map (fun c => (2622750721-1+2*2^9*c.k,100007919094566+c.lower,100008299456714+c.upper)) = pointBounds19980 := by
 decide +kernel
def cuts19981 : List PrefixCut := [⟨14,70827791,70827833⟩,
⟨95,478616581,478616857⟩,
⟨128,647737857,647738234⟩]
theorem checked19981 : checkPrefixCuts (2^48) 2622881793 9 Manual.Count131072.C019981.packed 128 cuts19981 = true := by
 decide +kernel
def pointBounds19981 : List (Nat × Nat × Nat) := [(2622896128,100008639839087,100009020201663),(2622979072,100009047627877,100009427990687)]
theorem point_links_checked19981 : (cuts19981.take 2).map (fun c => (2622881793-1+2*2^9*c.k,100008569011296+c.lower,100008949373830+c.upper)) = pointBounds19981 := by
 decide +kernel
def cuts19982 : List PrefixCut := [⟨48,250029403,250029548⟩,
⟨128,650924863,650925243⟩]
theorem checked19982 : checkPrefixCuts (2^48) 2623012865 9 Manual.Count131072.C019982.packed 128 cuts19982 = true := by
 decide +kernel
def pointBounds19982 : List (Nat × Nat × Nat) := [(2623062016,100009466778556,100009847141612)]
theorem point_links_checked19982 : (cuts19982.take 1).map (fun c => (2623012865-1+2*2^9*c.k,100009216749153+c.lower,100009597112064+c.upper)) = pointBounds19982 := by
 decide +kernel
def cuts19983 : List PrefixCut := [⟨1,4828697,4828700⟩,
⟨82,407213682,407213928⟩,
⟨128,641664179,641664565⟩]
theorem checked19983 : checkPrefixCuts (2^48) 2623143937 9 Manual.Count131072.C019983.packed 128 cuts19983 = true := by
 decide +kernel
def pointBounds19983 : List (Nat × Nat × Nat) := [(2623144960,100009872502713,100010252866007),(2623227904,100010274887698,100010655251235)]
theorem point_links_checked19983 : (cuts19983.take 2).map (fun c => (2623143937-1+2*2^9*c.k,100009867674016+c.lower,100010248037307+c.upper)) = pointBounds19983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000311
