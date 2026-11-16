import PlattAssemblyKernel
import PlattCertificates.Count131072.C019664
import PlattCertificates.Count131072.C019665
import PlattCertificates.Count131072.C019666
import PlattCertificates.Count131072.C019667
import PlattCertificates.Count131072.C019668
import PlattCertificates.Count131072.C019669
import PlattCertificates.Count131072.C019670
import PlattCertificates.Count131072.C019671
import PlattCertificates.Count131072.C019672
import PlattCertificates.Count131072.C019673
import PlattCertificates.Count131072.C019674
import PlattCertificates.Count131072.C019675
import PlattCertificates.Count131072.C019676
import PlattCertificates.Count131072.C019677
import PlattCertificates.Count131072.C019678
import PlattCertificates.Count131072.C019679
import PlattCertificates.Count131072.C019680
import PlattCertificates.Count131072.C019681
import PlattCertificates.Count131072.C019682
import PlattCertificates.Count131072.C019683
import PlattCertificates.Count131072.C019684
import PlattCertificates.Count131072.C019685
import PlattCertificates.Count131072.C019686
import PlattCertificates.Count131072.C019687
import PlattCertificates.Count131072.C019688
import PlattCertificates.Count131072.C019689
import PlattCertificates.Count131072.C019690
import PlattCertificates.Count131072.C019691
import PlattCertificates.Count131072.C019692
import PlattCertificates.Count131072.C019693
import PlattCertificates.Count131072.C019694
import PlattCertificates.Count131072.C019695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19664 : List PrefixCut := [⟨24,123326480,123326555⟩,
⟨103,524483772,524484085⟩,
⟨128,654020311,654020703⟩]
theorem checked19664 : checkPrefixCuts (2^48) 2581331969 9 Manual.Count131072.C019664.packed 128 cuts19664 = true := by
 decide +kernel
def pointBounds19664 : List (Nat × Nat × Nat) := [(2581356544,99801379259452,99801759499864),(2581437440,99801780416744,99802160657394)]
theorem point_links_checked19664 : (cuts19664.take 2).map (fun c => (2581331969-1+2*2^9*c.k,99801255932972+c.lower,99801636173309+c.upper)) = pointBounds19664 := by
 decide +kernel
def cuts19665 : List PrefixCut := [⟨54,282838856,282839020⟩,
⟨128,662382805,662383193⟩]
theorem checked19665 : checkPrefixCuts (2^48) 2581463041 9 Manual.Count131072.C019665.packed 128 cuts19665 = true := by
 decide +kernel
def pointBounds19665 : List (Nat × Nat × Nat) := [(2581518336,99802192792139,99802573033032)]
theorem point_links_checked19665 : (cuts19665.take 1).map (fun c => (2581463041-1+2*2^9*c.k,99801909953283+c.lower,99802290194012+c.upper)) = pointBounds19665 := by
 decide +kernel
def cuts19666 : List PrefixCut := [⟨5,27912017,27912033⟩,
⟨84,435900406,435900664⟩,
⟨128,664638735,664639125⟩]
theorem checked19666 : checkPrefixCuts (2^48) 2581594113 9 Manual.Count131072.C019666.packed 128 cuts19666 = true := by
 decide +kernel
def pointBounds19666 : List (Nat × Nat × Nat) := [(2581599232,99802600248105,99802980489238),(2581680128,99803008236494,99803388477869)]
theorem point_links_checked19666 : (cuts19666.take 2).map (fun c => (2581594113-1+2*2^9*c.k,99802572336088+c.lower,99802952577205+c.upper)) = pointBounds19666 := by
 decide +kernel
def cuts19667 : List PrefixCut := [⟨35,183053201,183053306⟩,
⟨114,597339351,597339695⟩,
⟨128,670492218,670492606⟩]
theorem checked19667 : checkPrefixCuts (2^48) 2581725185 9 Manual.Count131072.C019667.packed 128 cuts19667 = true := by
 decide +kernel
def pointBounds19667 : List (Nat × Nat × Nat) := [(2581761024,99803420028024,99803800269636),(2581841920,99803834314174,99804214556025)]
theorem point_links_checked19667 : (cuts19667.take 2).map (fun c => (2581725185-1+2*2^9*c.k,99803236974823+c.lower,99803617216330+c.upper)) = pointBounds19667 := by
 decide +kernel
def cuts19668 : List PrefixCut := [⟨65,334688254,334688446⟩,
⟨128,658030253,658030633⟩]
theorem checked19668 : checkPrefixCuts (2^48) 2581856257 9 Manual.Count131072.C019668.packed 128 cuts19668 = true := by
 decide +kernel
def pointBounds19668 : List (Nat × Nat × Nat) := [(2581922816,99804242155295,99804622397382)]
theorem point_links_checked19668 : (cuts19668.take 1).map (fun c => (2581856257-1+2*2^9*c.k,99803907467041+c.lower,99804287708936+c.upper)) = pointBounds19668 := by
 decide +kernel
def cuts19669 : List PrefixCut := [⟨16,80670712,80670759⟩,
⟨95,486960047,486960337⟩,
⟨128,656906651,656907039⟩]
theorem checked19669 : checkPrefixCuts (2^48) 2581987329 9 Manual.Count131072.C019669.packed 128 cuts19669 = true := by
 decide +kernel
def pointBounds19669 : List (Nat × Nat × Nat) := [(2582003712,99804646168006,99805026410328),(2582084608,99805052457341,99805432699906)]
theorem point_links_checked19669 : (cuts19669.take 2).map (fun c => (2581987329-1+2*2^9*c.k,99804565497294+c.lower,99804945739569+c.upper)) = pointBounds19669 := by
 decide +kernel
def cuts19670 : List PrefixCut := [⟨46,232732736,232732873⟩,
⟨125,642920737,642921116⟩,
⟨128,658617287,658617676⟩]
theorem checked19670 : checkPrefixCuts (2^48) 2582118401 9 Manual.Count131072.C019670.packed 128 cuts19670 = true := by
 decide +kernel
def pointBounds19670 : List (Nat × Nat × Nat) := [(2582165504,99805455136681,99805835379481),(2582246400,99805865324682,99806245567724)]
theorem point_links_checked19670 : (cuts19670.take 2).map (fun c => (2582118401-1+2*2^9*c.k,99805222403945+c.lower,99805602646608+c.upper)) = pointBounds19670 := by
 decide +kernel
def cuts19671 : List PrefixCut := [⟨76,389791603,389791830⟩,
⟨128,659891970,659892352⟩]
theorem checked19671 : checkPrefixCuts (2^48) 2582249473 9 Manual.Count131072.C019671.packed 128 cuts19671 = true := by
 decide +kernel
def pointBounds19671 : List (Nat × Nat × Nat) := [(2582327296,99806270812835,99806651056114)]
theorem point_links_checked19671 : (cuts19671.take 1).map (fun c => (2582249473-1+2*2^9*c.k,99805881021232+c.lower,99806261264284+c.upper)) = pointBounds19671 := by
 decide +kernel
def cuts19672 : List PrefixCut := [⟨27,141151943,141152027⟩,
⟨106,549339521,549339847⟩,
⟨128,657024765,657025155⟩]
theorem checked19672 : checkPrefixCuts (2^48) 2582380545 9 Manual.Count131072.C019672.packed 128 cuts19672 = true := by
 decide +kernel
def pointBounds19672 : List (Nat × Nat × Nat) := [(2582408192,99806682065145,99807062308663),(2582489088,99807090252723,99807470496483)]
theorem point_links_checked19672 : (cuts19672.take 2).map (fun c => (2582380545-1+2*2^9*c.k,99806540913202+c.lower,99806921156636+c.upper)) = pointBounds19672 := by
 decide +kernel
def cuts19673 : List PrefixCut := [⟨57,291007189,291007360⟩,
⟨128,658953088,658953471⟩]
theorem checked19673 : checkPrefixCuts (2^48) 2582511617 9 Manual.Count131072.C019673.packed 128 cuts19673 = true := by
 decide +kernel
def pointBounds19673 : List (Nat × Nat × Nat) := [(2582569984,99807488945156,99807869189151)]
theorem point_links_checked19673 : (cuts19673.take 1).map (fun c => (2582511617-1+2*2^9*c.k,99807197937967+c.lower,99807578181791+c.upper)) = pointBounds19673 := by
 decide +kernel
def cuts19674 : List PrefixCut := [⟨8,41415056,41415082⟩,
⟨87,444333086,444333349⟩,
⟨128,652925639,652926026⟩]
theorem checked19674 : checkPrefixCuts (2^48) 2582642689 9 Manual.Count131072.C019674.packed 128 cuts19674 = true := by
 decide +kernel
def pointBounds19674 : List (Nat × Nat × Nat) := [(2582650880,99807898306111,99808278550344),(2582731776,99808301224141,99808681468611)]
theorem point_links_checked19674 : (cuts19674.take 2).map (fun c => (2582642689-1+2*2^9*c.k,99807856891055+c.lower,99808237135262+c.upper)) = pointBounds19674 := by
 decide +kernel
def cuts19675 : List PrefixCut := [⟨38,194857660,194857777⟩,
⟨117,604942991,604943349⟩,
⟨128,661719662,661720054⟩]
theorem checked19675 : checkPrefixCuts (2^48) 2582773761 9 Manual.Count131072.C019675.packed 128 cuts19675 = true := by
 decide +kernel
def pointBounds19675 : List (Nat × Nat × Nat) := [(2582812672,99808704674354,99809084919065),(2582893568,99809114759685,99809495004637)]
theorem point_links_checked19675 : (cuts19675.take 2).map (fun c => (2582773761-1+2*2^9*c.k,99808509816694+c.lower,99808890061288+c.upper)) = pointBounds19675 := by
 decide +kernel
def cuts19676 : List PrefixCut := [⟨68,349808585,349808793⟩,
⟨128,663211717,663212106⟩]
theorem checked19676 : checkPrefixCuts (2^48) 2582904833 9 Manual.Count131072.C019676.packed 128 cuts19676 = true := by
 decide +kernel
def pointBounds19676 : List (Nat × Nat × Nat) := [(2582974464,99809521344941,99809901590135)]
theorem point_links_checked19676 : (cuts19676.take 1).map (fun c => (2582904833-1+2*2^9*c.k,99809171536356+c.lower,99809551781342+c.upper)) = pointBounds19676 := by
 decide +kernel
def cuts19677 : List PrefixCut := [⟨19,97855199,97855259⟩,
⟨98,506158533,506158841⟩,
⟨128,660344995,660345395⟩]
theorem checked19677 : checkPrefixCuts (2^48) 2583035905 9 Manual.Count131072.C019677.packed 128 cuts19677 = true := by
 decide +kernel
def pointBounds19677 : List (Nat × Nat × Nat) := [(2583055360,99809932603272,99810312848707),(2583136256,99810340906606,99810721152289)]
theorem point_links_checked19677 : (cuts19677.take 2).map (fun c => (2583035905-1+2*2^9*c.k,99809834748073+c.lower,99810214993448+c.upper)) = pointBounds19677 := by
 decide +kernel
def cuts19678 : List PrefixCut := [⟨49,248219958,248220106⟩,
⟨128,650177986,650178370⟩]
theorem checked19678 : checkPrefixCuts (2^48) 2583166977 9 Manual.Count131072.C019678.packed 128 cuts19678 = true := by
 decide +kernel
def pointBounds19678 : List (Nat × Nat × Nat) := [(2583217152,99810743313026,99811123558949),(2583298048,99811145271054,99811525517213)]
theorem point_links_checked19678 : (cuts19678.take 2).map (fun c => (2583166977-1+2*2^9*c.k,99810495093068+c.lower,99810875338843+c.upper)) = pointBounds19678 := by
 decide +kernel
def cuts19679 : List PrefixCut := [⟨79,411751625,411751866⟩,
⟨128,668994451,668994842⟩]
theorem checked19679 : checkPrefixCuts (2^48) 2583298049 9 Manual.Count131072.C019679.packed 128 cuts19679 = true := by
 decide +kernel
def pointBounds19679 : List (Nat × Nat × Nat) := [(2583378944,99811557022679,99811937269079)]
theorem point_links_checked19679 : (cuts19679.take 1).map (fun c => (2583298049-1+2*2^9*c.k,99811145271054+c.lower,99811525517213+c.upper)) = pointBounds19679 := by
 decide +kernel
def cuts19680 : List PrefixCut := [⟨30,152425711,152425803⟩,
⟨109,554127986,554128317⟩,
⟨128,651855114,651855506⟩]
theorem checked19680 : checkPrefixCuts (2^48) 2583429121 9 Manual.Count131072.C019680.packed 128 cuts19680 = true := by
 decide +kernel
def pointBounds19680 : List (Nat × Nat × Nat) := [(2583459840,99811966691216,99812346937858),(2583540736,99812368393491,99812748640372)]
theorem point_links_checked19680 : (cuts19680.take 2).map (fun c => (2583429121-1+2*2^9*c.k,99811814265505+c.lower,99812194512055+c.upper)) = pointBounds19680 := by
 decide +kernel
def cuts19681 : List PrefixCut := [⟨60,307993599,307993776⟩,
⟨128,654218878,654219258⟩]
theorem checked19681 : checkPrefixCuts (2^48) 2583560193 9 Manual.Count131072.C019681.packed 128 cuts19681 = true := by
 decide +kernel
def pointBounds19681 : List (Nat × Nat × Nat) := [(2583621632,99812774114218,99813154361337)]
theorem point_links_checked19681 : (cuts19681.take 1).map (fun c => (2583560193-1+2*2^9*c.k,99812466120619+c.lower,99812846367561+c.upper)) = pointBounds19681 := by
 decide +kernel
def cuts19682 : List PrefixCut := [⟨11,55016060,55016093⟩,
⟨90,461691908,461692185⟩,
⟨128,660504167,660504563⟩]
theorem checked19682 : checkPrefixCuts (2^48) 2583691265 9 Manual.Count131072.C019682.packed 128 cuts19682 = true := by
 decide +kernel
def pointBounds19682 : List (Nat × Nat × Nat) := [(2583702528,99813175355557,99813555602912),(2583783424,99813582031405,99813962279004)]
theorem point_links_checked19682 : (cuts19682.take 2).map (fun c => (2583691265-1+2*2^9*c.k,99813120339497+c.lower,99813500586819+c.upper)) = pointBounds19682 := by
 decide +kernel
def cuts19683 : List PrefixCut := [⟨41,212535134,212535257⟩,
⟨120,614501347,614501708⟩,
⟨128,657638438,657638824⟩]
theorem checked19683 : checkPrefixCuts (2^48) 2583822337 9 Manual.Count131072.C019683.packed 128 cuts19683 = true := by
 decide +kernel
def pointBounds19683 : List (Nat × Nat × Nat) := [(2583864320,99813993378798,99814373626639),(2583945216,99814395345011,99814775593090)]
theorem point_links_checked19683 : (cuts19683.take 2).map (fun c => (2583822337-1+2*2^9*c.k,99813780843664+c.lower,99814161091382+c.upper)) = pointBounds19683 := by
 decide +kernel
def cuts19684 : List PrefixCut := [⟨71,364589875,364590087⟩,
⟨128,665338953,665339346⟩]
theorem checked19684 : checkPrefixCuts (2^48) 2583953409 9 Manual.Count131072.C019684.packed 128 cuts19684 = true := by
 decide +kernel
def pointBounds19684 : List (Nat × Nat × Nat) := [(2584026112,99814803071977,99815183320293)]
theorem point_links_checked19684 : (cuts19684.take 1).map (fun c => (2583953409-1+2*2^9*c.k,99814438482102+c.lower,99814818730206+c.upper)) = pointBounds19684 := by
 decide +kernel
def cuts19685 : List PrefixCut := [⟨22,114154321,114154390⟩,
⟨101,522835995,522836305⟩,
⟨128,659641299,659641689⟩]
theorem checked19685 : checkPrefixCuts (2^48) 2584084481 9 Manual.Count131072.C019685.packed 128 cuts19685 = true := by
 decide +kernel
def pointBounds19685 : List (Nat × Nat × Nat) := [(2584107008,99815217975376,99815598223942),(2584187904,99815626657050,99816006905857)]
theorem point_links_checked19685 : (cuts19685.take 2).map (fun c => (2584084481-1+2*2^9*c.k,99815103821055+c.lower,99815484069552+c.upper)) = pointBounds19685 := by
 decide +kernel
def cuts19686 : List PrefixCut := [⟨52,268813810,268813971⟩,
⟨128,657756213,657756605⟩]
theorem checked19686 : checkPrefixCuts (2^48) 2584215553 9 Manual.Count131072.C019686.packed 128 cuts19686 = true := by
 decide +kernel
def pointBounds19686 : List (Nat × Nat × Nat) := [(2584268800,99816032276164,99816412525212)]
theorem point_links_checked19686 : (cuts19686.take 1).map (fun c => (2584215553-1+2*2^9*c.k,99815763462354+c.lower,99816143711241+c.upper)) = pointBounds19686 := by
 decide +kernel
def cuts19687 : List PrefixCut := [⟨3,13941150,13941159⟩,
⟨82,419317148,419317402⟩,
⟨128,659138667,659139060⟩]
theorem checked19687 : checkPrefixCuts (2^48) 2584346625 9 Manual.Count131072.C019687.packed 128 cuts19687 = true := by
 decide +kernel
def pointBounds19687 : List (Nat × Nat × Nat) := [(2584349696,99816435159717,99816815409005),(2584430592,99816840535715,99817220785248)]
theorem point_links_checked19687 : (cuts19687.take 2).map (fun c => (2584346625-1+2*2^9*c.k,99816421218567+c.lower,99816801467846+c.upper)) = pointBounds19687 := by
 decide +kernel
def cuts19688 : List PrefixCut := [⟨33,165323951,165324048⟩,
⟨112,568605301,568605634⟩,
⟨128,648323463,648323844⟩]
theorem checked19688 : checkPrefixCuts (2^48) 2584477697 9 Manual.Count131072.C019688.packed 128 cuts19688 = true := by
 decide +kernel
def pointBounds19688 : List (Nat × Nat × Nat) := [(2584511488,99817245681185,99817625930954),(2584592384,99817648962535,99818029212540)]
theorem point_links_checked19688 : (cuts19688.take 2).map (fun c => (2584477697-1+2*2^9*c.k,99817080357234+c.lower,99817460606906+c.upper)) = pointBounds19688 := by
 decide +kernel
def cuts19689 : List PrefixCut := [⟨63,329213454,329213647⟩,
⟨128,666694982,666695374⟩]
theorem checked19689 : checkPrefixCuts (2^48) 2584608769 9 Manual.Count131072.C019689.packed 128 cuts19689 = true := by
 decide +kernel
def pointBounds19689 : List (Nat × Nat × Nat) := [(2584673280,99818057894151,99818438144397)]
theorem point_links_checked19689 : (cuts19689.take 1).map (fun c => (2584608769-1+2*2^9*c.k,99817728680697+c.lower,99818108930750+c.upper)) = pointBounds19689 := by
 decide +kernel
def cuts19690 : List PrefixCut := [⟨14,74595423,74595467⟩,
⟨93,479254571,479254844⟩,
⟨128,662849804,662850189⟩]
theorem checked19690 : checkPrefixCuts (2^48) 2584739841 9 Manual.Count131072.C019690.packed 128 cuts19690 = true := by
 decide +kernel
def pointBounds19690 : List (Nat × Nat × Nat) := [(2584754176,99818469971102,99818850221591),(2584835072,99818874630250,99819254880968)]
theorem point_links_checked19690 : (cuts19690.take 2).map (fun c => (2584739841-1+2*2^9*c.k,99818395375679+c.lower,99818775626124+c.upper)) = pointBounds19690 := by
 decide +kernel
def cuts19691 : List PrefixCut := [⟨44,223882468,223882603⟩,
⟨123,631347443,631347820⟩,
⟨128,657153850,657154243⟩]
theorem checked19691 : checkPrefixCuts (2^48) 2584870913 9 Manual.Count131072.C019691.packed 128 cuts19691 = true := by
 decide +kernel
def pointBounds19691 : List (Nat × Nat × Nat) := [(2584915968,99819282107951,99819662358916),(2584996864,99819689572926,99820069824133)]
theorem point_links_checked19691 : (cuts19691.take 2).map (fun c => (2584870913-1+2*2^9*c.k,99819058225483+c.lower,99819438476313+c.upper)) = pointBounds19691 := by
 decide +kernel
def cuts19692 : List PrefixCut := [⟨74,378270271,378270495⟩,
⟨128,658318216,658318606⟩]
theorem checked19692 : checkPrefixCuts (2^48) 2585001985 9 Manual.Count131072.C019692.packed 128 cuts19692 = true := by
 decide +kernel
def pointBounds19692 : List (Nat × Nat × Nat) := [(2585077760,99820093649604,99820473901051)]
theorem point_links_checked19692 : (cuts19692.take 1).map (fun c => (2585001985-1+2*2^9*c.k,99819715379333+c.lower,99820095630556+c.upper)) = pointBounds19692 := by
 decide +kernel
def cuts19693 : List PrefixCut := [⟨25,126629332,126629408⟩,
⟨104,536233598,536233921⟩,
⟨128,654691956,654692349⟩]
theorem checked19693 : checkPrefixCuts (2^48) 2585133057 9 Manual.Count131072.C019693.packed 128 cuts19693 = true := by
 decide +kernel
def pointBounds19693 : List (Nat × Nat × Nat) := [(2585158656,99820500326881,99820880578570),(2585239552,99820909931147,99821290183083)]
theorem point_links_checked19693 : (cuts19693.take 2).map (fun c => (2585133057-1+2*2^9*c.k,99820373697549+c.lower,99820753949162+c.upper)) = pointBounds19693 := by
 decide +kernel
def cuts19694 : List PrefixCut := [⟨55,281878558,281878723⟩,
⟨128,658578035,658578429⟩]
theorem checked19694 : checkPrefixCuts (2^48) 2585264129 9 Manual.Count131072.C019694.packed 128 cuts19694 = true := by
 decide +kernel
def pointBounds19694 : List (Nat × Nat × Nat) := [(2585320448,99821310268063,99821690520234)]
theorem point_links_checked19694 : (cuts19694.take 1).map (fun c => (2585264129-1+2*2^9*c.k,99821028389505+c.lower,99821408641511+c.upper)) = pointBounds19694 := by
 decide +kernel
def cuts19695 : List PrefixCut := [⟨6,29286298,29286314⟩,
⟨85,439505376,439505636⟩,
⟨128,662681763,662682154⟩]
theorem checked19695 : checkPrefixCuts (2^48) 2585395201 9 Manual.Count131072.C019695.packed 128 cuts19695 = true := by
 decide +kernel
def pointBounds19695 : List (Nat × Nat × Nat) := [(2585401344,99821716253838,99822096506254),(2585482240,99822126472916,99822506725576)]
theorem point_links_checked19695 : (cuts19695.take 2).map (fun c => (2585395201-1+2*2^9*c.k,99821686967540+c.lower,99822067219940+c.upper)) = pointBounds19695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000302
