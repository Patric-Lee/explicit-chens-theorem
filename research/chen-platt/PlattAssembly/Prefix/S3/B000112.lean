import PlattAssemblyKernel
import PlattCertificates.Count131072.C023584
import PlattCertificates.Count131072.C023585
import PlattCertificates.Count131072.C023586
import PlattCertificates.Count131072.C023587
import PlattCertificates.Count131072.C023588
import PlattCertificates.Count131072.C023589
import PlattCertificates.Count131072.C023590
import PlattCertificates.Count131072.C023591
import PlattCertificates.Count131072.C023592
import PlattCertificates.Count131072.C023593
import PlattCertificates.Count131072.C023594
import PlattCertificates.Count131072.C023595
import PlattCertificates.Count131072.C023596
import PlattCertificates.Count131072.C023597
import PlattCertificates.Count131072.C023598
import PlattCertificates.Count131072.C023599
import PlattCertificates.Count131072.C023600
import PlattCertificates.Count131072.C023601
import PlattCertificates.Count131072.C023602
import PlattCertificates.Count131072.C023603
import PlattCertificates.Count131072.C023604
import PlattCertificates.Count131072.C023605
import PlattCertificates.Count131072.C023606
import PlattCertificates.Count131072.C023607
import PlattCertificates.Count131072.C023608
import PlattCertificates.Count131072.C023609
import PlattCertificates.Count131072.C023610
import PlattCertificates.Count131072.C023611
import PlattCertificates.Count131072.C023612
import PlattCertificates.Count131072.C023613
import PlattCertificates.Count131072.C023614
import PlattCertificates.Count131072.C023615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23584 : List PrefixCut := [⟨86,365214291,365214492⟩,
⟨128,539996906,539997210⟩]
theorem checked23584 : checkPrefixCuts (2^48) 3095134209 9 Manual.Count131072.C023584.packed 128 cuts23584 = true := by
 decide +kernel
def pointBounds23584 : List (Nat × Nat × Nat) := [(3095222272,102149342991892,102149724586349)]
theorem point_links_checked23584 : (cuts23584.take 1).map (fun c => (3095134209-1+2*2^9*c.k,102148977777601+c.lower,102149359371857+c.upper)) = pointBounds23584 := by
 decide +kernel
def cuts23585 : List PrefixCut := [⟨53,234070439,234070566⟩,
⟨128,552341258,552341566⟩]
theorem checked23585 : checkPrefixCuts (2^48) 3095265281 9 Manual.Count131072.C023585.packed 128 cuts23585 = true := by
 decide +kernel
def pointBounds23585 : List (Nat × Nat × Nat) := [(3095319552,102149751844946,102150133439633)]
theorem point_links_checked23585 : (cuts23585.take 1).map (fun c => (3095265281-1+2*2^9*c.k,102149517774507+c.lower,102149899369067+c.upper)) = pointBounds23585 := by
 decide +kernel
def cuts23586 : List PrefixCut := [⟨20,83294713,83294759⟩,
⟨115,487393637,487393917⟩,
⟨128,544679367,544679678⟩]
theorem checked23586 : checkPrefixCuts (2^48) 3095396353 9 Manual.Count131072.C023586.packed 128 cuts23586 = true := by
 decide +kernel
def pointBounds23586 : List (Nat × Nat × Nat) := [(3095416832,102150153410478,102150535005392),(3095514112,102150557509402,102150939104550)]
theorem point_links_checked23586 : (cuts23586.take 2).map (fun c => (3095396353-1+2*2^9*c.k,102150070115765+c.lower,102150451710633+c.upper)) = pointBounds23586 := by
 decide +kernel
def cuts23587 : List PrefixCut := [⟨82,348891899,348892100⟩,
⟨128,546565867,546566180⟩]
theorem checked23587 : checkPrefixCuts (2^48) 3095527425 9 Manual.Count131072.C023587.packed 128 cuts23587 = true := by
 decide +kernel
def pointBounds23587 : List (Nat × Nat × Nat) := [(3095611392,102150963687031,102151345282411)]
theorem point_links_checked23587 : (cuts23587.take 1).map (fun c => (3095527425-1+2*2^9*c.k,102150614795132+c.lower,102150996390311+c.upper)) = pointBounds23587 := by
 decide +kernel
def cuts23588 : List PrefixCut := [⟨49,207308898,207309011⟩,
⟨128,541996581,541996881⟩]
theorem checked23588 : checkPrefixCuts (2^48) 3095658497 9 Manual.Count131072.C023588.packed 128 cuts23588 = true := by
 decide +kernel
def pointBounds23588 : List (Nat × Nat × Nat) := [(3095708672,102151368669897,102151750265502)]
theorem point_links_checked23588 : (cuts23588.take 1).map (fun c => (3095658497-1+2*2^9*c.k,102151161360999+c.lower,102151542956491+c.upper)) = pointBounds23588 := by
 decide +kernel
def cuts23589 : List PrefixCut := [⟨16,69282266,69282303⟩,
⟨111,472966778,472967042⟩,
⟨128,545610464,545610770⟩]
theorem checked23589 : checkPrefixCuts (2^48) 3095789569 9 Manual.Count131072.C023589.packed 128 cuts23589 = true := by
 decide +kernel
def pointBounds23589 : List (Nat × Nat × Nat) := [(3095805952,102151772639846,102152154235675),(3095903232,102152176324358,102152557920414)]
theorem point_links_checked23589 : (cuts23589.take 2).map (fun c => (3095789569-1+2*2^9*c.k,102151703357580+c.lower,102152084953372+c.upper)) = pointBounds23589 := by
 decide +kernel
def cuts23590 : List PrefixCut := [⟨78,331937265,331937450⟩,
⟨128,543132588,543132893⟩]
theorem checked23590 : checkPrefixCuts (2^48) 3095920641 9 Manual.Count131072.C023590.packed 128 cuts23590 = true := by
 decide +kernel
def pointBounds23590 : List (Nat × Nat × Nat) := [(3096000512,102152580905309,102152962501592)]
theorem point_links_checked23590 : (cuts23590.take 1).map (fun c => (3095920641-1+2*2^9*c.k,102152248968044+c.lower,102152630564142+c.upper)) = pointBounds23590 := by
 decide +kernel
def cuts23591 : List PrefixCut := [⟨45,192281984,192282094⟩,
⟨128,549655238,549655548⟩]
theorem checked23591 : checkPrefixCuts (2^48) 3096051713 9 Manual.Count131072.C023591.packed 128 cuts23591 = true := by
 decide +kernel
def pointBounds23591 : List (Nat × Nat × Nat) := [(3096097792,102152984382616,102153365979129)]
theorem point_links_checked23591 : (cuts23591.take 1).map (fun c => (3096051713-1+2*2^9*c.k,102152792100632+c.lower,102153173697035+c.upper)) = pointBounds23591 := by
 decide +kernel
def cuts23592 : List PrefixCut := [⟨12,50455116,50455147⟩,
⟨107,456452542,456452802⟩,
⟨128,543813941,543814253⟩]
theorem checked23592 : checkPrefixCuts (2^48) 3096182785 9 Manual.Count131072.C023592.packed 128 cuts23592 = true := by
 decide +kernel
def pointBounds23592 : List (Nat × Nat × Nat) := [(3096195072,102153392210986,102153773807730),(3096292352,102153798208412,102154179805385)]
theorem point_links_checked23592 : (cuts23592.take 2).map (fun c => (3096182785-1+2*2^9*c.k,102153341755870+c.lower,102153723352583+c.upper)) = pointBounds23592 := by
 decide +kernel
def cuts23593 : List PrefixCut := [⟨74,312350719,312350900⟩,
⟨128,543608998,543609312⟩]
theorem checked23593 : checkPrefixCuts (2^48) 3096313857 9 Manual.Count131072.C023593.packed 128 cuts23593 = true := by
 decide +kernel
def pointBounds23593 : List (Nat × Nat × Nat) := [(3096389632,102154197920530,102154579517736)]
theorem point_links_checked23593 : (cuts23593.take 1).map (fun c => (3096313857-1+2*2^9*c.k,102153885569811+c.lower,102154267166836+c.upper)) = pointBounds23593 := by
 decide +kernel
def cuts23594 : List PrefixCut := [⟨41,172077444,172077548⟩,
⟨128,547585584,547585903⟩]
theorem checked23594 : checkPrefixCuts (2^48) 3096444929 9 Manual.Count131072.C023594.packed 128 cuts23594 = true := by
 decide +kernel
def pointBounds23594 : List (Nat × Nat × Nat) := [(3096486912,102154601256253,102154982853696)]
theorem point_links_checked23594 : (cuts23594.take 1).map (fun c => (3096444929-1+2*2^9*c.k,102154429178809+c.lower,102154810776148+c.upper)) = pointBounds23594 := by
 decide +kernel
def cuts23595 : List PrefixCut := [⟨8,34814178,34814196⟩,
⟨103,437760928,437761167⟩,
⟨128,546289896,546290199⟩]
theorem checked23595 : checkPrefixCuts (2^48) 3096576001 9 Manual.Count131072.C023595.packed 128 cuts23595 = true := by
 decide +kernel
def pointBounds23595 : List (Nat × Nat × Nat) := [(3096584192,102155011578571,102155393176247),(3096681472,102155414525321,102155796123218)]
theorem point_links_checked23595 : (cuts23595.take 2).map (fun c => (3096576001-1+2*2^9*c.k,102154976764393+c.lower,102155358362051+c.upper)) = pointBounds23595 := by
 decide +kernel
def cuts23596 : List PrefixCut := [⟨70,293859827,293859994⟩,
⟨128,538359135,538359446⟩]
theorem checked23596 : checkPrefixCuts (2^48) 3096707073 9 Manual.Count131072.C023596.packed 128 cuts23596 = true := by
 decide +kernel
def pointBounds23596 : List (Nat × Nat × Nat) := [(3096778752,102155816914116,102156198512244)]
theorem point_links_checked23596 : (cuts23596.take 1).map (fun c => (3096707073-1+2*2^9*c.k,102155523054289+c.lower,102155904652250+c.upper)) = pointBounds23596 := by
 decide +kernel
def cuts23597 : List PrefixCut := [⟨37,160239981,160240071⟩,
⟨128,552787727,552788047⟩]
theorem checked23597 : checkPrefixCuts (2^48) 3096838145 9 Manual.Count131072.C023597.packed 128 cuts23597 = true := by
 decide +kernel
def pointBounds23597 : List (Nat × Nat × Nat) := [(3096876032,102156221653405,102156603251767)]
theorem point_links_checked23597 : (cuts23597.take 1).map (fun c => (3096838145-1+2*2^9*c.k,102156061413424+c.lower,102156443011696+c.upper)) = pointBounds23597 := by
 decide +kernel
def cuts23598 : List PrefixCut := [⟨4,14723719,14723727⟩,
⟨99,427435520,427435762⟩,
⟨128,551673680,551673998⟩]
theorem checked23598 : checkPrefixCuts (2^48) 3096969217 9 Manual.Count131072.C023598.packed 128 cuts23598 = true := by
 decide +kernel
def pointBounds23598 : List (Nat × Nat × Nat) := [(3096973312,102156628924870,102157010523470),(3097070592,102157041636671,102157423235505)]
theorem point_links_checked23598 : (cuts23598.take 2).map (fun c => (3096969217-1+2*2^9*c.k,102156614201151+c.lower,102156995799743+c.upper)) = pointBounds23598 := by
 decide +kernel
def cuts23599 : List PrefixCut := [⟨66,280008624,280008781⟩,
⟨128,544561609,544561911⟩]
theorem checked23599 : checkPrefixCuts (2^48) 3097100289 9 Manual.Count131072.C023599.packed 128 cuts23599 = true := by
 decide +kernel
def pointBounds23599 : List (Nat × Nat × Nat) := [(3097167872,102157445883455,102157827482522)]
theorem point_links_checked23599 : (cuts23599.take 1).map (fun c => (3097100289-1+2*2^9*c.k,102157165874831+c.lower,102157547473741+c.upper)) = pointBounds23599 := by
 decide +kernel
def cuts23600 : List PrefixCut := [⟨33,139044907,139044987⟩,
⟨128,539267644,539267942⟩]
theorem checked23600 : checkPrefixCuts (2^48) 3097231361 9 Manual.Count131072.C023600.packed 128 cuts23600 = true := by
 decide +kernel
def pointBounds23600 : List (Nat × Nat × Nat) := [(3097265152,102157849481347,102158231080639),(3097362432,102158249704084,102158631303594)]
theorem point_links_checked23600 : (cuts23600.take 2).map (fun c => (3097231361-1+2*2^9*c.k,102157710436440+c.lower,102158092035652+c.upper)) = pointBounds23600 := by
 decide +kernel
def cuts23601 : List PrefixCut := [⟨95,406207923,406208154⟩,
⟨128,546423914,546424223⟩]
theorem checked23601 : checkPrefixCuts (2^48) 3097362433 9 Manual.Count131072.C023601.packed 128 cuts23601 = true := by
 decide +kernel
def pointBounds23601 : List (Nat × Nat × Nat) := [(3097459712,102158655912007,102159037511748)]
theorem point_links_checked23601 : (cuts23601.take 1).map (fun c => (3097362433-1+2*2^9*c.k,102158249704084+c.lower,102158631303594+c.upper)) = pointBounds23601 := by
 decide +kernel
def cuts23602 : List PrefixCut := [⟨62,263889095,263889244⟩,
⟨128,543129453,543129758⟩]
theorem checked23602 : checkPrefixCuts (2^48) 3097493505 9 Manual.Count131072.C023602.packed 128 cuts23602 = true := by
 decide +kernel
def pointBounds23602 : List (Nat × Nat × Nat) := [(3097556992,102159060017093,102159441617061)]
theorem point_links_checked23602 : (cuts23602.take 1).map (fun c => (3097493505-1+2*2^9*c.k,102158796127998+c.lower,102159177727817+c.upper)) = pointBounds23602 := by
 decide +kernel
def cuts23603 : List PrefixCut := [⟨29,125578949,125579018⟩,
⟨124,529931250,529931549⟩,
⟨128,547104583,547104892⟩]
theorem checked23603 : checkPrefixCuts (2^48) 3097624577 9 Manual.Count131072.C023603.packed 128 cuts23603 = true := by
 decide +kernel
def pointBounds23603 : List (Nat × Nat × Nat) := [(3097654272,102159464836400,102159846436593),(3097751552,102159869188701,102160250789124)]
theorem point_links_checked23603 : (cuts23603.take 2).map (fun c => (3097624577-1+2*2^9*c.k,102159339257451+c.lower,102159720857575+c.upper)) = pointBounds23603 := by
 decide +kernel
def cuts23604 : List PrefixCut := [⟨91,379533793,379534010⟩,
⟨128,536813910,536814218⟩]
theorem checked23604 : checkPrefixCuts (2^48) 3097755649 9 Manual.Count131072.C023604.packed 128 cuts23604 = true := by
 decide +kernel
def pointBounds23604 : List (Nat × Nat × Nat) := [(3097848832,102160265895827,102160647496477)]
theorem point_links_checked23604 : (cuts23604.take 1).map (fun c => (3097755649-1+2*2^9*c.k,102159886362034+c.lower,102160267962467+c.upper)) = pointBounds23604 := by
 decide +kernel
def cuts23605 : List PrefixCut := [⟨58,246774193,246774329⟩,
⟨128,547694273,547694575⟩]
theorem checked23605 : checkPrefixCuts (2^48) 3097886721 9 Manual.Count131072.C023605.packed 128 cuts23605 = true := by
 decide +kernel
def pointBounds23605 : List (Nat × Nat × Nat) := [(3097946112,102160669950137,102161051551014)]
theorem point_links_checked23605 : (cuts23605.take 1).map (fun c => (3097886721-1+2*2^9*c.k,102160423175944+c.lower,102160804776685+c.upper)) = pointBounds23605 := by
 decide +kernel
def cuts23606 : List PrefixCut := [⟨25,103939356,103939413⟩,
⟨120,511420739,511421029⟩,
⟨128,544763690,544764000⟩]
theorem checked23606 : checkPrefixCuts (2^48) 3098017793 9 Manual.Count131072.C023606.packed 128 cuts23606 = true := by
 decide +kernel
def pointBounds23606 : List (Nat × Nat × Nat) := [(3098043392,102161074809573,102161456410673),(3098140672,102161482290956,102161863892289)]
theorem point_links_checked23606 : (cuts23606.take 2).map (fun c => (3098017793-1+2*2^9*c.k,102160970870217+c.lower,102161352471260+c.upper)) = pointBounds23606 := by
 decide +kernel
def cuts23607 : List PrefixCut := [⟨87,368492850,368493055⟩,
⟨128,541288373,541288675⟩]
theorem checked23607 : checkPrefixCuts (2^48) 3098148865 9 Manual.Count131072.C023607.packed 128 cuts23607 = true := by
 decide +kernel
def pointBounds23607 : List (Nat × Nat × Nat) := [(3098237952,102161884126757,102162265728315)]
theorem point_links_checked23607 : (cuts23607.take 1).map (fun c => (3098148865-1+2*2^9*c.k,102161515633907+c.lower,102161897235260+c.upper)) = pointBounds23607 := by
 decide +kernel
def cuts23608 : List PrefixCut := [⟨54,229209397,229209532⟩,
⟨128,544172568,544172882⟩]
theorem checked23608 : checkPrefixCuts (2^48) 3098279937 9 Manual.Count131072.C023608.packed 128 cuts23608 = true := by
 decide +kernel
def pointBounds23608 : List (Nat × Nat × Nat) := [(3098335232,102162286131677,102162667733467)]
theorem point_links_checked23608 : (cuts23608.take 1).map (fun c => (3098279937-1+2*2^9*c.k,102162056922280+c.lower,102162438523935+c.upper)) = pointBounds23608 := by
 decide +kernel
def cuts23609 : List PrefixCut := [⟨21,86484067,86484116⟩,
⟨116,489917198,489917486⟩,
⟨128,540788303,540788621⟩]
theorem checked23609 : checkPrefixCuts (2^48) 3098411009 9 Manual.Count131072.C023609.packed 128 cuts23609 = true := by
 decide +kernel
def pointBounds23609 : List (Nat × Nat × Nat) := [(3098432512,102162687578915,102163069180933),(3098529792,102163091012046,102163472614303)]
theorem point_links_checked23609 : (cuts23609.take 2).map (fun c => (3098411009-1+2*2^9*c.k,102162601094848+c.lower,102162982696817+c.upper)) = pointBounds23609 := by
 decide +kernel
def cuts23610 : List PrefixCut := [⟨83,351640936,351641133⟩,
⟨128,543218090,543218397⟩]
theorem checked23610 : checkPrefixCuts (2^48) 3098542081 9 Manual.Count131072.C023610.packed 128 cuts23610 = true := by
 decide +kernel
def pointBounds23610 : List (Nat × Nat × Nat) := [(3098627072,102163493524087,102163875126571)]
theorem point_links_checked23610 : (cuts23610.take 1).map (fun c => (3098542081-1+2*2^9*c.k,102163141883151+c.lower,102163523485438+c.upper)) = pointBounds23610 := by
 decide +kernel
def cuts23611 : List PrefixCut := [⟨50,213284041,213284166⟩,
⟨128,548281858,548282180⟩]
theorem checked23611 : checkPrefixCuts (2^48) 3098673153 9 Manual.Count131072.C023611.packed 128 cuts23611 = true := by
 decide +kernel
def pointBounds23611 : List (Nat × Nat × Nat) := [(3098724352,102163898385282,102164279988001)]
theorem point_links_checked23611 : (cuts23611.take 1).map (fun c => (3098673153-1+2*2^9*c.k,102163685101241+c.lower,102164066703835+c.upper)) = pointBounds23611 := by
 decide +kernel
def cuts23612 : List PrefixCut := [⟨17,72303179,72303221⟩,
⟨112,474141531,474141800⟩,
⟨128,541628061,541628369⟩]
theorem checked23612 : checkPrefixCuts (2^48) 3098804225 9 Manual.Count131072.C023612.packed 128 cuts23612 = true := by
 decide +kernel
def pointBounds23612 : List (Nat × Nat × Nat) := [(3098821632,102164305686278,102164687289236),(3098918912,102164707524630,102165089127815)]
theorem point_links_checked23612 : (cuts23612.take 2).map (fun c => (3098804225-1+2*2^9*c.k,102164233383099+c.lower,102164614986015+c.upper)) = pointBounds23612 := by
 decide +kernel
def cuts23613 : List PrefixCut := [⟨79,336155777,336155962⟩,
⟨128,544329968,544330271⟩]
theorem checked23613 : checkPrefixCuts (2^48) 3098935297 9 Manual.Count131072.C023613.packed 128 cuts23613 = true := by
 decide +kernel
def pointBounds23613 : List (Nat × Nat × Nat) := [(3099016192,102165111166937,102165492770346)]
theorem point_links_checked23613 : (cuts23613.take 1).map (fun c => (3098935297-1+2*2^9*c.k,102164775011160+c.lower,102165156614384+c.upper)) = pointBounds23613 := by
 decide +kernel
def cuts23614 : List PrefixCut := [⟨46,196454507,196454621⟩,
⟨128,548666485,548666801⟩]
theorem checked23614 : checkPrefixCuts (2^48) 3099066369 9 Manual.Count131072.C023614.packed 128 cuts23614 = true := by
 decide +kernel
def pointBounds23614 : List (Nat × Nat × Nat) := [(3099113472,102165515795635,102165897399276)]
theorem point_links_checked23614 : (cuts23614.take 1).map (fun c => (3099066369-1+2*2^9*c.k,102165319341128+c.lower,102165700944655+c.upper)) = pointBounds23614 := by
 decide +kernel
def cuts23615 : List PrefixCut := [⟨13,57490116,57490149⟩,
⟨108,457915788,457916059⟩,
⟨128,545192196,545192516⟩]
theorem checked23615 : checkPrefixCuts (2^48) 3099197441 9 Manual.Count131072.C023615.packed 128 cuts23615 = true := by
 decide +kernel
def pointBounds23615 : List (Nat × Nat × Nat) := [(3099210752,102165925497729,102166307101605),(3099308032,102166325923401,102166707527515)]
theorem point_links_checked23615 : (cuts23615.take 2).map (fun c => (3099197441-1+2*2^9*c.k,102165868007613+c.lower,102166249611456+c.upper)) = pointBounds23615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000112
