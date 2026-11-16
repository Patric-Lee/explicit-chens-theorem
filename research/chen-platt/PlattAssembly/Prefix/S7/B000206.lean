import PlattAssemblyKernel
import PlattCertificates.Count131072.C066592
import PlattCertificates.Count131072.C066593
import PlattCertificates.Count131072.C066594
import PlattCertificates.Count131072.C066595
import PlattCertificates.Count131072.C066596
import PlattCertificates.Count131072.C066597
import PlattCertificates.Count131072.C066598
import PlattCertificates.Count131072.C066599
import PlattCertificates.Count131072.C066600
import PlattCertificates.Count131072.C066601
import PlattCertificates.Count131072.C066602
import PlattCertificates.Count131072.C066603
import PlattCertificates.Count131072.C066604
import PlattCertificates.Count131072.C066605
import PlattCertificates.Count131072.C066606
import PlattCertificates.Count131072.C066607
import PlattCertificates.Count131072.C066608
import PlattCertificates.Count131072.C066609
import PlattCertificates.Count131072.C066610
import PlattCertificates.Count131072.C066611
import PlattCertificates.Count131072.C066612
import PlattCertificates.Count131072.C066613
import PlattCertificates.Count131072.C066614
import PlattCertificates.Count131072.C066615
import PlattCertificates.Count131072.C066616
import PlattCertificates.Count131072.C066617
import PlattCertificates.Count131072.C066618
import PlattCertificates.Count131072.C066619
import PlattCertificates.Count131072.C066620
import PlattCertificates.Count131072.C066621
import PlattCertificates.Count131072.C066622
import PlattCertificates.Count131072.C066623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000206
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66592 : List PrefixCut := [⟨64,180701560,180701661⟩]
theorem checked66592 : checkPrefixCuts (2^48) 8732278785 10 Manual.Count131072.C066592.packed 64 cuts66592 = true := by
 decide +kernel
def cuts66593 : List PrefixCut := [⟨12,33877212,33877230⟩,
⟨64,183374189,183374298⟩]
theorem checked66593 : checkPrefixCuts (2^48) 8732409857 10 Manual.Count131072.C066593.packed 64 cuts66593 = true := by
 decide +kernel
def pointBounds66593 : List (Nat × Nat × Nat) := [(8732434432,115201189327314,115201578474050)]
theorem point_links_checked66593 : (cuts66593.take 1).map (fun c => (8732409857-1+2*2^10*c.k,115201155450102+c.lower,115201544596820+c.upper)) = pointBounds66593 := by
 decide +kernel
def cuts66594 : List PrefixCut := [⟨64,183403675,183403782⟩]
theorem checked66594 : checkPrefixCuts (2^48) 8732540929 10 Manual.Count131072.C066594.packed 64 cuts66594 = true := by
 decide +kernel
def cuts66595 : List PrefixCut := [⟨18,52409756,52409785⟩,
⟨64,185689416,185689517⟩]
theorem checked66595 : checkPrefixCuts (2^48) 8732672001 10 Manual.Count131072.C066595.packed 64 cuts66595 = true := by
 decide +kernel
def pointBounds66595 : List (Nat × Nat × Nat) := [(8732708864,115201574637722,115201963784685)]
theorem point_links_checked66595 : (cuts66595.take 1).map (fun c => (8732672001-1+2*2^10*c.k,115201522227966+c.lower,115201911374900+c.upper)) = pointBounds66595 := by
 decide +kernel
def cuts66596 : List PrefixCut := [⟨64,184268432,184268542⟩]
theorem checked66596 : checkPrefixCuts (2^48) 8732803073 10 Manual.Count131072.C066596.packed 64 cuts66596 = true := by
 decide +kernel
def cuts66597 : List PrefixCut := [⟨24,69329593,69329637⟩,
⟨64,185393749,185393858⟩]
theorem checked66597 : checkPrefixCuts (2^48) 8732934145 10 Manual.Count131072.C066597.packed 64 cuts66597 = true := by
 decide +kernel
def pointBounds66597 : List (Nat × Nat × Nat) := [(8732983296,115201961515407,115202350662596)]
theorem point_links_checked66597 : (cuts66597.take 1).map (fun c => (8732934145-1+2*2^10*c.k,115201892185814+c.lower,115202281332959+c.upper)) = pointBounds66597 := by
 decide +kernel
def cuts66598 : List PrefixCut := [⟨64,184875278,184875387⟩]
theorem checked66598 : checkPrefixCuts (2^48) 8733065217 10 Manual.Count131072.C066598.packed 64 cuts66598 = true := by
 decide +kernel
def cuts66599 : List PrefixCut := [⟨30,85732711,85732758⟩,
⟨64,185452646,185452747⟩]
theorem checked66599 : checkPrefixCuts (2^48) 8733196289 10 Manual.Count131072.C066599.packed 64 cuts66599 = true := by
 decide +kernel
def pointBounds66599 : List (Nat × Nat × Nat) := [(8733257728,115202348187552,115202737334962)]
theorem point_links_checked66599 : (cuts66599.take 1).map (fun c => (8733196289-1+2*2^10*c.k,115202262454841+c.lower,115202651602204+c.upper)) = pointBounds66599 := by
 decide +kernel
def cuts66600 : List PrefixCut := [⟨64,185224266,185224374⟩]
theorem checked66600 : checkPrefixCuts (2^48) 8733327361 10 Manual.Count131072.C066600.packed 64 cuts66600 = true := by
 decide +kernel
def cuts66601 : List PrefixCut := [⟨36,103875202,103875263⟩,
⟨64,184738042,184738146⟩]
theorem checked66601 : checkPrefixCuts (2^48) 8733458433 10 Manual.Count131072.C066601.packed 64 cuts66601 = true := by
 decide +kernel
def pointBounds66601 : List (Nat × Nat × Nat) := [(8733532160,115202737006955,115203126154588)]
theorem point_links_checked66601 : (cuts66601.take 1).map (fun c => (8733458433-1+2*2^10*c.k,115202633131753+c.lower,115203022279325+c.upper)) = pointBounds66601 := by
 decide +kernel
def cuts66602 : List PrefixCut := [⟨64,184606335,184606438⟩]
theorem checked66602 : checkPrefixCuts (2^48) 8733589505 10 Manual.Count131072.C066602.packed 64 cuts66602 = true := by
 decide +kernel
def cuts66603 : List PrefixCut := [⟨42,118922655,118922728⟩,
⟨64,184925844,184925956⟩]
theorem checked66603 : checkPrefixCuts (2^48) 8733720577 10 Manual.Count131072.C066603.packed 64 cuts66603 = true := by
 decide +kernel
def pointBounds66603 : List (Nat × Nat × Nat) := [(8733806592,115203121398785,115203510546637)]
theorem point_links_checked66603 : (cuts66603.take 1).map (fun c => (8733720577-1+2*2^10*c.k,115203002476130+c.lower,115203391623909+c.upper)) = pointBounds66603 := by
 decide +kernel
def cuts66604 : List PrefixCut := [⟨64,185374275,185374381⟩]
theorem checked66604 : checkPrefixCuts (2^48) 8733851649 10 Manual.Count131072.C066604.packed 64 cuts66604 = true := by
 decide +kernel
def cuts66605 : List PrefixCut := [⟨48,140833613,140833695⟩,
⟨64,187820768,187820878⟩]
theorem checked66605 : checkPrefixCuts (2^48) 8733982721 10 Manual.Count131072.C066605.packed 64 cuts66605 = true := by
 decide +kernel
def pointBounds66605 : List (Nat × Nat × Nat) := [(8734081024,115203513609862,115203902757941)]
theorem point_links_checked66605 : (cuts66605.take 1).map (fun c => (8733982721-1+2*2^10*c.k,115203372776249+c.lower,115203761924246+c.upper)) = pointBounds66605 := by
 decide +kernel
def cuts66606 : List PrefixCut := [⟨64,186496663,186496774⟩]
theorem checked66606 : checkPrefixCuts (2^48) 8734113793 10 Manual.Count131072.C066606.packed 64 cuts66606 = true := by
 decide +kernel
def cuts66607 : List PrefixCut := [⟨54,153397579,153397668⟩,
⟨64,182368879,182368986⟩]
theorem checked66607 : checkPrefixCuts (2^48) 8734244865 10 Manual.Count131072.C066607.packed 64 cuts66607 = true := by
 decide +kernel
def pointBounds66607 : List (Nat × Nat × Nat) := [(8734355456,115203900491259,115204289639566)]
theorem point_links_checked66607 : (cuts66607.take 1).map (fun c => (8734244865-1+2*2^10*c.k,115203747093680+c.lower,115204136241898+c.upper)) = pointBounds66607 := by
 decide +kernel
def cuts66608 : List PrefixCut := [⟨64,180303679,180303787⟩]
theorem checked66608 : checkPrefixCuts (2^48) 8734375937 10 Manual.Count131072.C066608.packed 64 cuts66608 = true := by
 decide +kernel
def cuts66609 : List PrefixCut := [⟨60,175080555,175080659⟩,
⟨64,186359357,186359468⟩]
theorem checked66609 : checkPrefixCuts (2^48) 8734507009 10 Manual.Count131072.C066609.packed 64 cuts66609 = true := by
 decide +kernel
def pointBounds66609 : List (Nat × Nat × Nat) := [(8734629888,115204284846793,115204673995330)]
theorem point_links_checked66609 : (cuts66609.take 1).map (fun c => (8734507009-1+2*2^10*c.k,115204109766238+c.lower,115204498914671+c.upper)) = pointBounds66609 := by
 decide +kernel
def cuts66610 : List PrefixCut := [⟨64,185583164,185583273⟩]
theorem checked66610 : checkPrefixCuts (2^48) 8734638081 10 Manual.Count131072.C066610.packed 64 cuts66610 = true := by
 decide +kernel
def cuts66611 : List PrefixCut := [⟨64,186418204,186418317⟩]
theorem checked66611 : checkPrefixCuts (2^48) 8734769153 10 Manual.Count131072.C066611.packed 64 cuts66611 = true := by
 decide +kernel
def cuts66612 : List PrefixCut := [⟨2,5284763,5284765⟩,
⟨64,182580761,182580869⟩]
theorem checked66612 : checkPrefixCuts (2^48) 8734900225 10 Manual.Count131072.C066612.packed 64 cuts66612 = true := by
 decide +kernel
def pointBounds66612 : List (Nat × Nat × Nat) := [(8734904320,115204673411726,115205062560494)]
theorem point_links_checked66612 : (cuts66612.take 1).map (fun c => (8734900225-1+2*2^10*c.k,115204668126963+c.lower,115205057275729+c.upper)) = pointBounds66612 := by
 decide +kernel
def cuts66613 : List PrefixCut := [⟨64,184189211,184189309⟩]
theorem checked66613 : checkPrefixCuts (2^48) 8735031297 10 Manual.Count131072.C066613.packed 64 cuts66613 = true := by
 decide +kernel
def cuts66614 : List PrefixCut := [⟨8,22298434,22298447⟩,
⟨64,184057538,184057646⟩]
theorem checked66614 : checkPrefixCuts (2^48) 8735162369 10 Manual.Count131072.C066614.packed 64 cuts66614 = true := by
 decide +kernel
def pointBounds66614 : List (Nat × Nat × Nat) := [(8735178752,115205057195369,115205446344354)]
theorem point_links_checked66614 : (cuts66614.take 1).map (fun c => (8735162369-1+2*2^10*c.k,115205034896935+c.lower,115205424045907+c.upper)) = pointBounds66614 := by
 decide +kernel
def cuts66615 : List PrefixCut := [⟨64,186471465,186471566⟩]
theorem checked66615 : checkPrefixCuts (2^48) 8735293441 10 Manual.Count131072.C066615.packed 64 cuts66615 = true := by
 decide +kernel
def cuts66616 : List PrefixCut := [⟨14,40052171,40052195⟩,
⟨64,186371999,186372107⟩]
theorem checked66616 : checkPrefixCuts (2^48) 8735424513 10 Manual.Count131072.C066616.packed 64 cuts66616 = true := by
 decide +kernel
def pointBounds66616 : List (Nat × Nat × Nat) := [(8735453184,115205445478109,115205834627314)]
theorem point_links_checked66616 : (cuts66616.take 1).map (fun c => (8735424513-1+2*2^10*c.k,115205405425938+c.lower,115205794575119+c.upper)) = pointBounds66616 := by
 decide +kernel
def cuts66617 : List PrefixCut := [⟨64,185982551,185982663⟩]
theorem checked66617 : checkPrefixCuts (2^48) 8735555585 10 Manual.Count131072.C066617.packed 64 cuts66617 = true := by
 decide +kernel
def cuts66618 : List PrefixCut := [⟨20,57418165,57418199⟩,
⟨64,185528656,185528764⟩]
theorem checked66618 : checkPrefixCuts (2^48) 8735686657 10 Manual.Count131072.C066618.packed 64 cuts66618 = true := by
 decide +kernel
def pointBounds66618 : List (Nat × Nat × Nat) := [(8735727616,115205835198653,115206224348088)]
theorem point_links_checked66618 : (cuts66618.take 1).map (fun c => (8735686657-1+2*2^10*c.k,115205777780488+c.lower,115206166929889+c.upper)) = pointBounds66618 := by
 decide +kernel
def cuts66619 : List PrefixCut := [⟨64,185010376,185010479⟩]
theorem checked66619 : checkPrefixCuts (2^48) 8735817729 10 Manual.Count131072.C066619.packed 64 cuts66619 = true := by
 decide +kernel
def cuts66620 : List PrefixCut := [⟨26,76877401,76877446⟩,
⟨64,185523103,185523214⟩]
theorem checked66620 : checkPrefixCuts (2^48) 8735948801 10 Manual.Count131072.C066620.packed 64 cuts66620 = true := by
 decide +kernel
def pointBounds66620 : List (Nat × Nat × Nat) := [(8736002048,115206225196921,115206614346578)]
theorem point_links_checked66620 : (cuts66620.take 1).map (fun c => (8735948801-1+2*2^10*c.k,115206148319520+c.lower,115206537469132+c.upper)) = pointBounds66620 := by
 decide +kernel
def cuts66621 : List PrefixCut := [⟨64,185616976,185617084⟩]
theorem checked66621 : checkPrefixCuts (2^48) 8736079873 10 Manual.Count131072.C066621.packed 64 cuts66621 = true := by
 decide +kernel
def cuts66622 : List PrefixCut := [⟨32,92533580,92533630⟩,
⟨64,184905371,184905475⟩]
theorem checked66622 : checkPrefixCuts (2^48) 8736210945 10 Manual.Count131072.C066622.packed 64 cuts66622 = true := by
 decide +kernel
def pointBounds66622 : List (Nat × Nat × Nat) := [(8736276480,115206611993179,115207001143060)]
theorem point_links_checked66622 : (cuts66622.take 1).map (fun c => (8736210945-1+2*2^10*c.k,115206519459599+c.lower,115206908609430+c.upper)) = pointBounds66622 := by
 decide +kernel
def cuts66623 : List PrefixCut := [⟨64,183549425,183549533⟩]
theorem checked66623 : checkPrefixCuts (2^48) 8736342017 10 Manual.Count131072.C066623.packed 64 cuts66623 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000206
