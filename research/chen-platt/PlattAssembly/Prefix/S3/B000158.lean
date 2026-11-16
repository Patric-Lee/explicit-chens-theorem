import PlattAssemblyKernel
import PlattCertificates.Count131072.C025056
import PlattCertificates.Count131072.C025057
import PlattCertificates.Count131072.C025058
import PlattCertificates.Count131072.C025059
import PlattCertificates.Count131072.C025060
import PlattCertificates.Count131072.C025061
import PlattCertificates.Count131072.C025062
import PlattCertificates.Count131072.C025063
import PlattCertificates.Count131072.C025064
import PlattCertificates.Count131072.C025065
import PlattCertificates.Count131072.C025066
import PlattCertificates.Count131072.C025067
import PlattCertificates.Count131072.C025068
import PlattCertificates.Count131072.C025069
import PlattCertificates.Count131072.C025070
import PlattCertificates.Count131072.C025071
import PlattCertificates.Count131072.C025072
import PlattCertificates.Count131072.C025073
import PlattCertificates.Count131072.C025074
import PlattCertificates.Count131072.C025075
import PlattCertificates.Count131072.C025076
import PlattCertificates.Count131072.C025077
import PlattCertificates.Count131072.C025078
import PlattCertificates.Count131072.C025079
import PlattCertificates.Count131072.C025080
import PlattCertificates.Count131072.C025081
import PlattCertificates.Count131072.C025082
import PlattCertificates.Count131072.C025083
import PlattCertificates.Count131072.C025084
import PlattCertificates.Count131072.C025085
import PlattCertificates.Count131072.C025086
import PlattCertificates.Count131072.C025087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25056 : List PrefixCut := [⟨64,254671854,254671990⟩,
⟨128,506171355,506171630⟩]
theorem checked25056 : checkPrefixCuts (2^48) 3288072193 9 Manual.Count131072.C025056.packed 128 cuts25056 = true := by
 decide +kernel
def pointBounds25056 : List (Nat × Nat × Nat) := [(3288137728,102926969738482,102927351771192)]
theorem point_links_checked25056 : (cuts25056.take 1).map (fun c => (3288072193-1+2*2^9*c.k,102926715066628+c.lower,102927097099202+c.upper)) = pointBounds25056 := by
 decide +kernel
def cuts25057 : List PrefixCut := [⟨37,146548811,146548892⟩,
⟨128,518563106,518563389⟩]
theorem checked25057 : checkPrefixCuts (2^48) 3288203265 9 Manual.Count131072.C025057.packed 128 cuts25057 = true := by
 decide +kernel
def pointBounds25057 : List (Nat × Nat × Nat) := [(3288241152,102927367786794,102927749819724)]
theorem point_links_checked25057 : (cuts25057.take 1).map (fun c => (3288203265-1+2*2^9*c.k,102927221237983+c.lower,102927603270832+c.upper)) = pointBounds25057 := by
 decide +kernel
def cuts25058 : List PrefixCut := [⟨10,40573395,40573420⟩,
⟨111,445615598,445615853⟩,
⟨128,513749087,513749380⟩]
theorem checked25058 : checkPrefixCuts (2^48) 3288334337 9 Manual.Count131072.C025058.packed 128 cuts25058 = true := by
 decide +kernel
def pointBounds25058 : List (Nat × Nat × Nat) := [(3288344576,102927780374484,102928162407641),(3288448000,102928185416687,102928567450074)]
theorem point_links_checked25058 : (cuts25058.take 2).map (fun c => (3288334337-1+2*2^9*c.k,102927739801089+c.lower,102928121834221+c.upper)) = pointBounds25058 := by
 decide +kernel
def cuts25059 : List PrefixCut := [⟨84,340234113,340234303⟩,
⟨128,515012519,515012808⟩]
theorem checked25059 : checkPrefixCuts (2^48) 3288465409 9 Manual.Count131072.C025059.packed 128 cuts25059 = true := by
 decide +kernel
def pointBounds25059 : List (Nat × Nat × Nat) := [(3288551424,102928593784289,102928975817904)]
theorem point_links_checked25059 : (cuts25059.take 1).map (fun c => (3288465409-1+2*2^9*c.k,102928253550176+c.lower,102928635583601+c.upper)) = pointBounds25059 := by
 decide +kernel
def cuts25060 : List PrefixCut := [⟨57,227756136,227756269⟩,
⟨128,508401585,508401881⟩]
theorem checked25060 : checkPrefixCuts (2^48) 3288596481 9 Manual.Count131072.C025060.packed 128 cuts25060 = true := by
 decide +kernel
def pointBounds25060 : List (Nat × Nat × Nat) := [(3288654848,102928996318831,102929378352678)]
theorem point_links_checked25060 : (cuts25060.take 1).map (fun c => (3288596481-1+2*2^9*c.k,102928768562695+c.lower,102929150596409+c.upper)) = pointBounds25060 := by
 decide +kernel
def cuts25061 : List PrefixCut := [⟨30,123160241,123160308⟩,
⟨128,516854414,516854697⟩]
theorem checked25061 : checkPrefixCuts (2^48) 3288727553 9 Manual.Count131072.C025061.packed 128 cuts25061 = true := by
 decide +kernel
def pointBounds25061 : List (Nat × Nat × Nat) := [(3288758272,102929400124521,102929782158598)]
theorem point_links_checked25061 : (cuts25061.take 1).map (fun c => (3288727553-1+2*2^9*c.k,102929276964280+c.lower,102929658998290+c.upper)) = pointBounds25061 := by
 decide +kernel
def cuts25062 : List PrefixCut := [⟨3,11810638,11810644⟩,
⟨104,418843146,418843381⟩,
⟨128,510415115,510415400⟩]
theorem checked25062 : checkPrefixCuts (2^48) 3288858625 9 Manual.Count131072.C025062.packed 128 cuts25062 = true := by
 decide +kernel
def pointBounds25062 : List (Nat × Nat × Nat) := [(3288861696,102929805629332,102930187663631),(3288965120,102930212661840,102930594696368)]
theorem point_links_checked25062 : (cuts25062.take 2).map (fun c => (3288858625-1+2*2^9*c.k,102929793818694+c.lower,102930175852987+c.upper)) = pointBounds25062 := by
 decide +kernel
def cuts25063 : List PrefixCut := [⟨77,303723192,303723369⟩,
⟨128,509966721,509967017⟩]
theorem checked25063 : checkPrefixCuts (2^48) 3288989697 9 Manual.Count131072.C025063.packed 128 cuts25063 = true := by
 decide +kernel
def pointBounds25063 : List (Nat × Nat × Nat) := [(3289068544,102930607957001,102930989991756)]
theorem point_links_checked25063 : (cuts25063.take 1).map (fun c => (3288989697-1+2*2^9*c.k,102930304233809+c.lower,102930686268387+c.upper)) = pointBounds25063 := by
 decide +kernel
def cuts25064 : List PrefixCut := [⟨50,199736465,199736575⟩,
⟨128,508406155,508406438⟩]
theorem checked25064 : checkPrefixCuts (2^48) 3289120769 9 Manual.Count131072.C025064.packed 128 cuts25064 = true := by
 decide +kernel
def pointBounds25064 : List (Nat × Nat × Nat) := [(3289171968,102931013936995,102931395971979)]
theorem point_links_checked25064 : (cuts25064.take 1).map (fun c => (3289120769-1+2*2^9*c.k,102930814200530+c.lower,102931196235404+c.upper)) = pointBounds25064 := by
 decide +kernel
def cuts25065 : List PrefixCut := [⟨23,89938102,89938158⟩,
⟨124,501540299,501540591⟩,
⟨128,517028610,517028911⟩]
theorem checked25065 : checkPrefixCuts (2^48) 3289251841 9 Manual.Count131072.C025065.packed 128 cuts25065 = true := by
 decide +kernel
def pointBounds25065 : List (Nat × Nat × Nat) := [(3289275392,102931412544787,102931794580000),(3289378816,102931824146984,102932206182433)]
theorem point_links_checked25065 : (cuts25065.take 2).map (fun c => (3289251841-1+2*2^9*c.k,102931322606685+c.lower,102931704641842+c.upper)) = pointBounds25065 := by
 decide +kernel
def cuts25066 : List PrefixCut := [⟨97,387201714,387201930⟩,
⟨128,511617188,511617473⟩]
theorem checked25066 : checkPrefixCuts (2^48) 3289382913 9 Manual.Count131072.C025066.packed 128 cuts25066 = true := by
 decide +kernel
def pointBounds25066 : List (Nat × Nat × Nat) := [(3289482240,102932226837009,102932608872683)]
theorem point_links_checked25066 : (cuts25066.take 1).map (fun c => (3289382913-1+2*2^9*c.k,102931839635295+c.lower,102932221670753+c.upper)) = pointBounds25066 := by
 decide +kernel
def cuts25067 : List PrefixCut := [⟨70,281513412,281513568⟩,
⟨128,515789512,515789799⟩]
theorem checked25067 : checkPrefixCuts (2^48) 3289513985 9 Manual.Count131072.C025067.packed 128 cuts25067 = true := by
 decide +kernel
def pointBounds25067 : List (Nat × Nat × Nat) := [(3289585664,102932632765895,102933014801794)]
theorem point_links_checked25067 : (cuts25067.take 1).map (fun c => (3289513985-1+2*2^9*c.k,102932351252483+c.lower,102932733288226+c.upper)) = pointBounds25067 := by
 decide +kernel
def cuts25068 : List PrefixCut := [⟨43,174720335,174720432⟩,
⟨128,510549722,510550010⟩]
theorem checked25068 : checkPrefixCuts (2^48) 3289645057 9 Manual.Count131072.C025068.packed 128 cuts25068 = true := by
 decide +kernel
def pointBounds25068 : List (Nat × Nat × Nat) := [(3289689088,102933041762330,102933423798457)]
theorem point_links_checked25068 : (cuts25068.take 1).map (fun c => (3289645057-1+2*2^9*c.k,102932867041995+c.lower,102933249078025+c.upper)) = pointBounds25068 := by
 decide +kernel
def cuts25069 : List PrefixCut := [⟨16,62373451,62373487⟩,
⟨117,466381754,466382020⟩,
⟨128,509417045,509417336⟩]
theorem checked25069 : checkPrefixCuts (2^48) 3289776129 9 Manual.Count131072.C025069.packed 128 cuts25069 = true := by
 decide +kernel
def pointBounds25069 : List (Nat × Nat × Nat) := [(3289792512,102933439965168,102933822001522),(3289895936,102933843973471,102934226010055)]
theorem point_links_checked25069 : (cuts25069.take 2).map (fun c => (3289776129-1+2*2^9*c.k,102933377591717+c.lower,102933759628035+c.upper)) = pointBounds25069 := by
 decide +kernel
def cuts25070 : List PrefixCut := [⟨90,356425844,356426043⟩,
⟨128,509054528,509054813⟩]
theorem checked25070 : checkPrefixCuts (2^48) 3289907201 9 Manual.Count131072.C025070.packed 128 cuts25070 = true := by
 decide +kernel
def pointBounds25070 : List (Nat × Nat × Nat) := [(3289999360,102934243434606,102934625471414)]
theorem point_links_checked25070 : (cuts25070.take 1).map (fun c => (3289907201-1+2*2^9*c.k,102933887008762+c.lower,102934269045371+c.upper)) = pointBounds25070 := by
 decide +kernel
def cuts25071 : List PrefixCut := [⟨63,252295354,252295501⟩,
⟨128,513739644,513739941⟩]
theorem checked25071 : checkPrefixCuts (2^48) 3290038273 9 Manual.Count131072.C025071.packed 128 cuts25071 = true := by
 decide +kernel
def pointBounds25071 : List (Nat × Nat × Nat) := [(3290102784,102934648358644,102935030395685)]
theorem point_links_checked25071 : (cuts25071.take 1).map (fun c => (3290038273-1+2*2^9*c.k,102934396063290+c.lower,102934778100184+c.upper)) = pointBounds25071 := by
 decide +kernel
def cuts25072 : List PrefixCut := [⟨36,139873928,139874006⟩,
⟨128,507645195,507645480⟩]
theorem checked25072 : checkPrefixCuts (2^48) 3290169345 9 Manual.Count131072.C025072.packed 128 cuts25072 = true := by
 decide +kernel
def pointBounds25072 : List (Nat × Nat × Nat) := [(3290206208,102935049676862,102935431714131)]
theorem point_links_checked25072 : (cuts25072.take 1).map (fun c => (3290169345-1+2*2^9*c.k,102934909802934+c.lower,102935291840125+c.upper)) = pointBounds25072 := by
 decide +kernel
def cuts25073 : List PrefixCut := [⟨9,35501901,35501921⟩,
⟨110,436880341,436880589⟩,
⟨128,509079222,509079509⟩]
theorem checked25073 : checkPrefixCuts (2^48) 3290300417 9 Manual.Count131072.C025073.packed 128 cuts25073 = true := by
 decide +kernel
def pointBounds25073 : List (Nat × Nat × Nat) := [(3290309632,102935452950030,102935834987526),(3290413056,102935854328470,102936236366194)]
theorem point_links_checked25073 : (cuts25073.take 2).map (fun c => (3290300417-1+2*2^9*c.k,102935417448129+c.lower,102935799485605+c.upper)) = pointBounds25073 := by
 decide +kernel
def cuts25074 : List PrefixCut := [⟨83,332845321,332845505⟩,
⟨128,508374733,508375015⟩]
theorem checked25074 : checkPrefixCuts (2^48) 3290431489 9 Manual.Count131072.C025074.packed 128 cuts25074 = true := by
 decide +kernel
def pointBounds25074 : List (Nat × Nat × Nat) := [(3290516480,102936259372672,102936641410619)]
theorem point_links_checked25074 : (cuts25074.take 1).map (fun c => (3290431489-1+2*2^9*c.k,102935926527351+c.lower,102936308565114+c.upper)) = pointBounds25074 := by
 decide +kernel
def cuts25075 : List PrefixCut := [⟨56,222316676,222316799⟩,
⟨128,506558120,506558407⟩]
theorem checked25075 : checkPrefixCuts (2^48) 3290562561 9 Manual.Count131072.C025075.packed 128 cuts25075 = true := by
 decide +kernel
def pointBounds25075 : List (Nat × Nat × Nat) := [(3290619904,102936657218760,102937039256928)]
theorem point_links_checked25075 : (cuts25075.take 1).map (fun c => (3290562561-1+2*2^9*c.k,102936434902084+c.lower,102936816940129+c.upper)) = pointBounds25075 := by
 decide +kernel
def cuts25076 : List PrefixCut := [⟨29,116329303,116329372⟩,
⟨128,505597063,505597353⟩]
theorem checked25076 : checkPrefixCuts (2^48) 3290693633 9 Manual.Count131072.C025076.packed 128 cuts25076 = true := by
 decide +kernel
def pointBounds25076 : List (Nat × Nat × Nat) := [(3290723328,102937057789507,102937439827908)]
theorem point_links_checked25076 : (cuts25076.take 1).map (fun c => (3290693633-1+2*2^9*c.k,102936941460204+c.lower,102937323498536+c.upper)) = pointBounds25076 := by
 decide +kernel
def cuts25077 : List PrefixCut := [⟨2,8040121,8040127⟩,
⟨103,412862365,412862600⟩,
⟨128,513360312,513360604⟩]
theorem checked25077 : checkPrefixCuts (2^48) 3290824705 9 Manual.Count131072.C025077.packed 128 cuts25077 = true := by
 decide +kernel
def pointBounds25077 : List (Nat × Nat × Nat) := [(3290826752,102937455097388,102937837136016),(3290930176,102937859919632,102938241958489)]
theorem point_links_checked25077 : (cuts25077.take 2).map (fun c => (3290824705-1+2*2^9*c.k,102937447057267+c.lower,102937829095889+c.upper)) = pointBounds25077 := by
 decide +kernel
def cuts25078 : List PrefixCut := [⟨76,300890375,300890541⟩,
⟨128,512484462,512484746⟩]
theorem checked25078 : checkPrefixCuts (2^48) 3290955777 9 Manual.Count131072.C025078.packed 128 cuts25078 = true := by
 decide +kernel
def pointBounds25078 : List (Nat × Nat × Nat) := [(3291033600,102938261307954,102938643347034)]
theorem point_links_checked25078 : (cuts25078.take 1).map (fun c => (3290955777-1+2*2^9*c.k,102937960417579+c.lower,102938342456493+c.upper)) = pointBounds25078 := by
 decide +kernel
def cuts25079 : List PrefixCut := [⟨49,195426399,195426507⟩,
⟨128,514431176,514431463⟩]
theorem checked25079 : checkPrefixCuts (2^48) 3291086849 9 Manual.Count131072.C025079.packed 128 cuts25079 = true := by
 decide +kernel
def pointBounds25079 : List (Nat × Nat × Nat) := [(3291137024,102938668328440,102939050367746)]
theorem point_links_checked25079 : (cuts25079.take 1).map (fun c => (3291086849-1+2*2^9*c.k,102938472902041+c.lower,102938854941239+c.upper)) = pointBounds25079 := by
 decide +kernel
def cuts25080 : List PrefixCut := [⟨22,85950349,85950398⟩,
⟨123,493201806,493202085⟩,
⟨128,513127891,513128182⟩]
theorem checked25080 : checkPrefixCuts (2^48) 3291217921 9 Manual.Count131072.C025080.packed 128 cuts25080 = true := by
 decide +kernel
def pointBounds25080 : List (Nat × Nat × Nat) := [(3291240448,102939073283566,102939455323100),(3291343872,102939480535023,102939862574787)]
theorem point_links_checked25080 : (cuts25080.take 2).map (fun c => (3291217921-1+2*2^9*c.k,102938987333217+c.lower,102939369372702+c.upper)) = pointBounds25080 := by
 decide +kernel
def cuts25081 : List PrefixCut := [⟨96,381326231,381326441⟩,
⟨128,511653585,511653865⟩]
theorem checked25081 : checkPrefixCuts (2^48) 3291348993 9 Manual.Count131072.C025081.packed 128 cuts25081 = true := by
 decide +kernel
def pointBounds25081 : List (Nat × Nat × Nat) := [(3291447296,102939881787339,102940263827325)]
theorem point_links_checked25081 : (cuts25081.take 1).map (fun c => (3291348993-1+2*2^9*c.k,102939500461108+c.lower,102939882500884+c.upper)) = pointBounds25081 := by
 decide +kernel
def cuts25082 : List PrefixCut := [⟨69,275273737,275273894⟩,
⟨128,511547781,511548076⟩]
theorem checked25082 : checkPrefixCuts (2^48) 3291480065 9 Manual.Count131072.C025082.packed 128 cuts25082 = true := by
 decide +kernel
def pointBounds25082 : List (Nat × Nat × Nat) := [(3291550720,102940287388430,102940669428643)]
theorem point_links_checked25082 : (cuts25082.take 1).map (fun c => (3291480065-1+2*2^9*c.k,102940012114693+c.lower,102940394154749+c.upper)) = pointBounds25082 := by
 decide +kernel
def cuts25083 : List PrefixCut := [⟨42,170169373,170169469⟩,
⟨128,513066648,513066938⟩]
theorem checked25083 : checkPrefixCuts (2^48) 3291611137 9 Manual.Count131072.C025083.packed 128 cuts25083 = true := by
 decide +kernel
def pointBounds25083 : List (Nat × Nat × Nat) := [(3291654144,102940693831847,102941075872294)]
theorem point_links_checked25083 : (cuts25083.take 1).map (fun c => (3291611137-1+2*2^9*c.k,102940523662474+c.lower,102940905702825+c.upper)) = pointBounds25083 := by
 decide +kernel
def cuts25084 : List PrefixCut := [⟨15,59941951,59941985⟩,
⟨116,464735240,464735506⟩,
⟨128,511934636,511934929⟩]
theorem checked25084 : checkPrefixCuts (2^48) 3291742209 9 Manual.Count131072.C025084.packed 128 cuts25084 = true := by
 decide +kernel
def pointBounds25084 : List (Nat × Nat × Nat) := [(3291757568,102941096671073,102941478711748),(3291860992,102941501464362,102941883505269)]
theorem point_links_checked25084 : (cuts25084.take 2).map (fun c => (3291742209-1+2*2^9*c.k,102941036729122+c.lower,102941418769763+c.upper)) = pointBounds25084 := by
 decide +kernel
def cuts25085 : List PrefixCut := [⟨89,358521650,358521853⟩,
⟨128,515590862,515591155⟩]
theorem checked25085 : checkPrefixCuts (2^48) 3291873281 9 Manual.Count131072.C025085.packed 128 cuts25085 = true := by
 decide +kernel
def pointBounds25085 : List (Nat × Nat × Nat) := [(3291964416,102941907185408,102942289226545)]
theorem point_links_checked25085 : (cuts25085.take 1).map (fun c => (3291873281-1+2*2^9*c.k,102941548663758+c.lower,102941930704692+c.upper)) = pointBounds25085 := by
 decide +kernel
def cuts25086 : List PrefixCut := [⟨62,242739526,242739660⟩,
⟨128,505823238,505823519⟩]
theorem checked25086 : checkPrefixCuts (2^48) 3292004353 9 Manual.Count131072.C025086.packed 128 cuts25086 = true := by
 decide +kernel
def pointBounds25086 : List (Nat × Nat × Nat) := [(3292067840,102942306994146,102942689035507)]
theorem point_links_checked25086 : (cuts25086.take 1).map (fun c => (3292004353-1+2*2^9*c.k,102942064254620+c.lower,102942446295847+c.upper)) = pointBounds25086 := by
 decide +kernel
def cuts25087 : List PrefixCut := [⟨35,136541456,136541533⟩,
⟨128,511360365,511360654⟩]
theorem checked25087 : checkPrefixCuts (2^48) 3292135425 9 Manual.Count131072.C025087.packed 128 cuts25087 = true := by
 decide +kernel
def pointBounds25087 : List (Nat × Nat × Nat) := [(3292171264,102942706619314,102943088660899)]
theorem point_links_checked25087 : (cuts25087.take 1).map (fun c => (3292135425-1+2*2^9*c.k,102942570077858+c.lower,102942952119366+c.upper)) = pointBounds25087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000158
