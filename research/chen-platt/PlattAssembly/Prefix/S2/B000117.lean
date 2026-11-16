import PlattAssemblyKernel
import PlattCertificates.Count131072.C013744
import PlattCertificates.Count131072.C013745
import PlattCertificates.Count131072.C013746
import PlattCertificates.Count131072.C013747
import PlattCertificates.Count131072.C013748
import PlattCertificates.Count131072.C013749
import PlattCertificates.Count131072.C013750
import PlattCertificates.Count131072.C013751
import PlattCertificates.Count131072.C013752
import PlattCertificates.Count131072.C013753
import PlattCertificates.Count131072.C013754
import PlattCertificates.Count131072.C013755
import PlattCertificates.Count131072.C013756
import PlattCertificates.Count131072.C013757
import PlattCertificates.Count131072.C013758
import PlattCertificates.Count131072.C013759
import PlattCertificates.Count131072.C013760
import PlattCertificates.Count131072.C013761
import PlattCertificates.Count131072.C013762
import PlattCertificates.Count131072.C013763
import PlattCertificates.Count131072.C013764
import PlattCertificates.Count131072.C013765
import PlattCertificates.Count131072.C013766
import PlattCertificates.Count131072.C013767
import PlattCertificates.Count131072.C013768
import PlattCertificates.Count131072.C013769
import PlattCertificates.Count131072.C013770
import PlattCertificates.Count131072.C013771
import PlattCertificates.Count131072.C013772
import PlattCertificates.Count131072.C013773
import PlattCertificates.Count131072.C013774
import PlattCertificates.Count131072.C013775
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13744 : List PrefixCut := [⟨43,329586371,329586597⟩,
⟨99,751301730,751302252⟩,
⟨128,966753346,966754022⟩]
theorem checked13744 : checkPrefixCuts (2^48) 1805385729 9 Manual.Count131072.C013744.packed 128 cuts13744 = true := by
 decide +kernel
def pointBounds13744 : List (Nat × Nat × Nat) := [(1805429760,95119171940675,95119549189475),(1805487104,95119593656034,95119970905130)]
theorem point_links_checked13744 : (cuts13744.take 2).map (fun c => (1805385729-1+2*2^9*c.k,95118842354304+c.lower,95119219602878+c.upper)) = pointBounds13744 := by
 decide +kernel
def cuts13745 : List PrefixCut := [⟨27,201261675,201261818⟩,
⟨83,626691678,626692118⟩,
⟨128,958888602,958889275⟩]
theorem checked13745 : checkPrefixCuts (2^48) 1805516801 9 Manual.Count131072.C013745.packed 128 cuts13745 = true := by
 decide +kernel
def pointBounds13745 : List (Nat × Nat × Nat) := [(1805544448,95120010369325,95120387618718),(1805601792,95120435799328,95120813049018)]
theorem point_links_checked13745 : (cuts13745.take 2).map (fun c => (1805516801-1+2*2^9*c.k,95119809107650+c.lower,95120186356900+c.upper)) = pointBounds13745 := by
 decide +kernel
def cuts13746 : List PrefixCut := [⟨11,80592708,80592764⟩,
⟨67,495395697,495396041⟩,
⟨123,925461352,925462000⟩,
⟨128,962247785,962248459⟩]
theorem checked13746 : checkPrefixCuts (2^48) 1805647873 9 Manual.Count131072.C013746.packed 128 cuts13746 = true := by
 decide +kernel
def pointBounds13746 : List (Nat × Nat × Nat) := [(1805659136,95120848588960,95121225838939),(1805716480,95121263391949,95121640642216),(1805773824,95121693457604,95122070708175)]
theorem point_links_checked13746 : (cuts13746.take 3).map (fun c => (1805647873-1+2*2^9*c.k,95120767996252+c.lower,95121145246175+c.upper)) = pointBounds13746 := by
 decide +kernel
def cuts13747 : List PrefixCut := [⟨51,383913277,383913546⟩,
⟨107,800702977,800703540⟩,
⟨128,964827891,964828568⟩]
theorem checked13747 : checkPrefixCuts (2^48) 1805778945 9 Manual.Count131072.C013747.packed 128 cuts13747 = true := by
 decide +kernel
def pointBounds13747 : List (Nat × Nat × Nat) := [(1805831168,95122114157314,95122491408180),(1805888512,95122530947014,95122908198174)]
theorem point_links_checked13747 : (cuts13747.take 2).map (fun c => (1805778945-1+2*2^9*c.k,95121730244037+c.lower,95122107494634+c.upper)) = pointBounds13747 := by
 decide +kernel
def cuts13748 : List PrefixCut := [⟨35,260756535,260756723⟩,
⟨91,682351386,682351868⟩,
⟨128,964290373,964291052⟩]
theorem checked13748 : checkPrefixCuts (2^48) 1805910017 9 Manual.Count131072.C013748.packed 128 cuts13748 = true := by
 decide +kernel
def pointBounds13748 : List (Nat × Nat × Nat) := [(1805945856,95122955828463,95123333079925),(1806003200,95123377423314,95123754675070)]
theorem point_links_checked13748 : (cuts13748.take 2).map (fun c => (1805910017-1+2*2^9*c.k,95122695071928+c.lower,95123072323202+c.upper)) = pointBounds13748 := by
 decide +kernel
def cuts13749 : List PrefixCut := [⟨19,140889350,140889449⟩,
⟨75,565574376,565574772⟩,
⟨128,952688184,952688852⟩]
theorem checked13749 : checkPrefixCuts (2^48) 1806041089 9 Manual.Count131072.C013749.packed 128 cuts13749 = true := by
 decide +kernel
def pointBounds13749 : List (Nat × Nat × Nat) := [(1806060544,95123800251651,95124177503703),(1806117888,95124224936677,95124602189026)]
theorem point_links_checked13749 : (cuts13749.take 2).map (fun c => (1806041089-1+2*2^9*c.k,95123659362301+c.lower,95124036614254+c.upper)) = pointBounds13749 := by
 decide +kernel
def cuts13750 : List PrefixCut := [⟨3,21038457,21038473⟩,
⟨59,444449752,444450062⟩,
⟨115,859432708,859433309⟩,
⟨128,959007973,959008643⟩]
theorem checked13750 : checkPrefixCuts (2^48) 1806172161 9 Manual.Count131072.C013750.packed 128 cuts13750 = true := by
 decide +kernel
def pointBounds13750 : List (Nat × Nat × Nat) := [(1806175232,95124633088942,95125010341579),(1806232576,95125056500237,95125433753168),(1806289920,95125471483193,95125848736415)]
theorem point_links_checked13750 : (cuts13750.take 3).map (fun c => (1806172161-1+2*2^9*c.k,95124612050485+c.lower,95124989303106+c.upper)) = pointBounds13750 := by
 decide +kernel
def cuts13751 : List PrefixCut := [⟨43,321939350,321939578⟩,
⟨99,738298367,738298883⟩,
⟨128,954731255,954731925⟩]
theorem checked13751 : checkPrefixCuts (2^48) 1806303233 9 Manual.Count131072.C013751.packed 128 cuts13751 = true := by
 decide +kernel
def pointBounds13751 : List (Nat × Nat × Nat) := [(1806347264,95125892997808,95126270251327),(1806404608,95126309356825,95126686610632)]
theorem point_links_checked13751 : (cuts13751.take 2).map (fun c => (1806303233-1+2*2^9*c.k,95125571058458+c.lower,95125948311749+c.upper)) = pointBounds13751 := by
 decide +kernel
def cuts13752 : List PrefixCut := [⟨27,199445483,199445623⟩,
⟨83,612038572,612039001⟩,
⟨128,957622051,957622719⟩]
theorem checked13752 : checkPrefixCuts (2^48) 1806434305 9 Manual.Count131072.C013752.packed 128 cuts13752 = true := by
 decide +kernel
def pointBounds13752 : List (Nat × Nat × Nat) := [(1806461952,95126725235196,95127102489297),(1806519296,95127137828285,95127515082675)]
theorem point_links_checked13752 : (cuts13752.take 2).map (fun c => (1806434305-1+2*2^9*c.k,95126525789713+c.lower,95126903043674+c.upper)) = pointBounds13752 := by
 decide +kernel
def cuts13753 : List PrefixCut := [⟨11,83979520,83979577⟩,
⟨67,502934374,502934725⟩,
⟨123,925926621,925927263⟩,
⟨128,964096534,964097203⟩]
theorem checked13753 : checkPrefixCuts (2^48) 1806565377 9 Manual.Count131072.C013753.packed 128 cuts13753 = true := by
 decide +kernel
def pointBounds13753 : List (Nat × Nat × Nat) := [(1806576640,95127567391284,95127944645970),(1806633984,95127986346138,95128363601118),(1806691328,95128409338385,95128786593656)]
theorem point_links_checked13753 : (cuts13753.take 3).map (fun c => (1806565377-1+2*2^9*c.k,95127483411764+c.lower,95127860666393+c.upper)) = pointBounds13753 := by
 decide +kernel
def cuts13754 : List PrefixCut := [⟨51,378732979,378733244⟩,
⟨107,793597341,793597899⟩,
⟨128,948759193,948759862⟩]
theorem checked13754 : checkPrefixCuts (2^48) 1806696449 9 Manual.Count131072.C013754.packed 128 cuts13754 = true := by
 decide +kernel
def pointBounds13754 : List (Nat × Nat × Nat) := [(1806748672,95128826241277,95129203496840),(1806806016,95129241105639,95129618361495)]
theorem point_links_checked13754 : (cuts13754.take 2).map (fun c => (1806696449-1+2*2^9*c.k,95128447508298+c.lower,95128824763596+c.upper)) = pointBounds13754 := by
 decide +kernel
def cuts13755 : List PrefixCut := [⟨35,259533641,259533823⟩,
⟨91,677487315,677487789⟩,
⟨128,955077279,955077950⟩]
theorem checked13755 : checkPrefixCuts (2^48) 1806827521 9 Manual.Count131072.C013755.packed 128 cuts13755 = true := by
 decide +kernel
def pointBounds13755 : List (Nat × Nat × Nat) := [(1806863360,95129655801132,95130033057281),(1806920704,95130073754806,95130451011247)]
theorem point_links_checked13755 : (cuts13755.take 2).map (fun c => (1806827521-1+2*2^9*c.k,95129396267491+c.lower,95129773523458+c.upper)) = pointBounds13755 := by
 decide +kernel
def cuts13756 : List PrefixCut := [⟨19,136456181,136456275⟩,
⟨75,561081394,561081783⟩,
⟨128,957655983,957656656⟩]
theorem checked13756 : checkPrefixCuts (2^48) 1806958593 9 Manual.Count131072.C013756.packed 128 cuts13756 = true := by
 decide +kernel
def pointBounds13756 : List (Nat × Nat × Nat) := [(1806978048,95130487800951,95130865057683),(1807035392,95130912426164,95131289683191)]
theorem point_links_checked13756 : (cuts13756.take 2).map (fun c => (1806958593-1+2*2^9*c.k,95130351344770+c.lower,95130728601408+c.upper)) = pointBounds13756 := by
 decide +kernel
def cuts13757 : List PrefixCut := [⟨3,23675718,23675734⟩,
⟨59,445937453,445937761⟩,
⟨115,861488447,861489043⟩,
⟨128,965841426,965842093⟩]
theorem checked13757 : checkPrefixCuts (2^48) 1807089665 9 Manual.Count131072.C013757.packed 128 cuts13757 = true := by
 decide +kernel
def pointBounds13757 : List (Nat × Nat × Nat) := [(1807092736,95131332676471,95131709933798),(1807150080,95131754938206,95132132195825),(1807207424,95132170489200,95132547747107)]
theorem point_links_checked13757 : (cuts13757.take 3).map (fun c => (1807089665-1+2*2^9*c.k,95131309000753+c.lower,95131686258064+c.upper)) = pointBounds13757 := by
 decide +kernel
def cuts13758 : List PrefixCut := [⟨43,318505139,318505365⟩,
⟨99,734652820,734653336⟩,
⟨128,946303643,946304310⟩]
theorem checked13758 : checkPrefixCuts (2^48) 1807220737 9 Manual.Count131072.C013758.packed 128 cuts13758 = true := by
 decide +kernel
def pointBounds13758 : List (Nat × Nat × Nat) := [(1807264768,95132593347318,95132970605522),(1807322112,95133009494999,95133386753493)]
theorem point_links_checked13758 : (cuts13758.take 2).map (fun c => (1807220737-1+2*2^9*c.k,95132274842179+c.lower,95132652100157+c.upper)) = pointBounds13758 := by
 decide +kernel
def cuts13759 : List PrefixCut := [⟨27,199655626,199655769⟩,
⟨83,623719293,623719732⟩,
⟨128,965545591,965546272⟩]
theorem checked13759 : checkPrefixCuts (2^48) 1807351809 9 Manual.Count131072.C013759.packed 128 cuts13759 = true := by
 decide +kernel
def pointBounds13759 : List (Nat × Nat × Nat) := [(1807379456,95133420801448,95133798060236),(1807436800,95133844865115,95134222124199)]
theorem point_links_checked13759 : (cuts13759.take 2).map (fun c => (1807351809-1+2*2^9*c.k,95133221145822+c.lower,95133598404467+c.upper)) = pointBounds13759 := by
 decide +kernel
def cuts13760 : List PrefixCut := [⟨11,80510892,80510948⟩,
⟨67,495671397,495671744⟩,
⟨123,915023048,915023686⟩,
⟨128,951149272,951149936⟩]
theorem checked13760 : checkPrefixCuts (2^48) 1807482881 9 Manual.Count131072.C013760.packed 128 cuts13760 = true := by
 decide +kernel
def pointBounds13760 : List (Nat × Nat × Nat) := [(1807494144,95134267202305,95134644461687),(1807551488,95134682362810,95135059622483),(1807608832,95135101714461,95135478974425)]
theorem point_links_checked13760 : (cuts13760.take 3).map (fun c => (1807482881-1+2*2^9*c.k,95134186691413+c.lower,95134563950739+c.upper)) = pointBounds13760 := by
 decide +kernel
def cuts13761 : List PrefixCut := [⟨51,391153663,391153933⟩,
⟨107,813904335,813904905⟩,
⟨128,972257238,972257917⟩]
theorem checked13761 : checkPrefixCuts (2^48) 1807613953 9 Manual.Count131072.C013761.packed 128 cuts13761 = true := by
 decide +kernel
def pointBounds13761 : List (Nat × Nat × Nat) := [(1807666176,95135528994348,95135906254608),(1807723520,95135951745020,95136329005580)]
theorem point_links_checked13761 : (cuts13761.take 2).map (fun c => (1807613953-1+2*2^9*c.k,95135137840685+c.lower,95135515100675+c.upper)) = pointBounds13761 := by
 decide +kernel
def cuts13762 : List PrefixCut := [⟨35,265162937,265163128⟩,
⟨91,676365131,676365611⟩,
⟨128,951945840,951946511⟩]
theorem checked13762 : checkPrefixCuts (2^48) 1807745025 9 Manual.Count131072.C013762.packed 128 cuts13762 = true := by
 decide +kernel
def pointBounds13762 : List (Nat × Nat × Nat) := [(1807780864,95136375260860,95136752521720),(1807838208,95136786463054,95137163724203)]
theorem point_links_checked13762 : (cuts13762.take 2).map (fun c => (1807745025-1+2*2^9*c.k,95136110097923+c.lower,95136487358592+c.upper)) = pointBounds13762 := by
 decide +kernel
def cuts13763 : List PrefixCut := [⟨19,141369096,141369194⟩,
⟨75,554724817,554725204⟩,
⟨128,950942487,950943153⟩]
theorem checked13763 : checkPrefixCuts (2^48) 1807876097 9 Manual.Count131072.C013763.packed 128 cuts13763 = true := by
 decide +kernel
def pointBounds13763 : List (Nat × Nat × Nat) := [(1807895552,95137203412859,95137580674297),(1807952896,95137616768580,95137994030307)]
theorem point_links_checked13763 : (cuts13763.take 2).map (fun c => (1807876097-1+2*2^9*c.k,95137062043763+c.lower,95137439305103+c.upper)) = pointBounds13763 := by
 decide +kernel
def cuts13764 : List PrefixCut := [⟨3,21328469,21328484⟩,
⟨59,435436326,435436636⟩,
⟨115,861673700,861674306⟩,
⟨128,958501478,958502151⟩]
theorem checked13764 : checkPrefixCuts (2^48) 1808007169 9 Manual.Count131072.C013764.packed 128 cuts13764 = true := by
 decide +kernel
def pointBounds13764 : List (Nat × Nat × Nat) := [(1808010240,95138034314719,95138411576740),(1808067584,95138448422576,95138825684892),(1808124928,95138874659950,95139251922562)]
theorem point_links_checked13764 : (cuts13764.take 3).map (fun c => (1808007169-1+2*2^9*c.k,95138012986250+c.lower,95138390248256+c.upper)) = pointBounds13764 := by
 decide +kernel
def cuts13765 : List PrefixCut := [⟨43,325971372,325971599⟩,
⟨99,745643681,745644202⟩,
⟨128,958743684,958744352⟩]
theorem checked13765 : checkPrefixCuts (2^48) 1808138241 9 Manual.Count131072.C013765.packed 128 cuts13765 = true := by
 decide +kernel
def pointBounds13765 : List (Nat × Nat × Nat) := [(1808182272,95139297459100,95139674722006),(1808239616,95139717131409,95140094394609)]
theorem point_links_checked13765 : (cuts13765.take 2).map (fun c => (1808138241-1+2*2^9*c.k,95138971487728+c.lower,95139348750407+c.upper)) = pointBounds13765 := by
 decide +kernel
def cuts13766 : List PrefixCut := [⟨27,200955322,200955463⟩,
⟨83,622935933,622936368⟩,
⟨128,959296723,959297395⟩]
theorem checked13766 : checkPrefixCuts (2^48) 1808269313 9 Manual.Count131072.C013766.packed 128 cuts13766 = true := by
 decide +kernel
def pointBounds13766 : List (Nat × Nat × Nat) := [(1808296960,95140131186734,95140508450222),(1808354304,95140553167345,95140930431127)]
theorem point_links_checked13766 : (cuts13766.take 2).map (fun c => (1808269313-1+2*2^9*c.k,95139930231412+c.lower,95140307494759+c.upper)) = pointBounds13766 := by
 decide +kernel
def cuts13767 : List PrefixCut := [⟨11,82026525,82026581⟩,
⟨67,504602935,504603288⟩,
⟨123,923430623,923431270⟩,
⟨128,959227244,959227915⟩]
theorem checked13767 : checkPrefixCuts (2^48) 1808400385 9 Manual.Count131072.C013767.packed 128 cuts13767 = true := by
 decide +kernel
def pointBounds13767 : List (Nat × Nat × Nat) := [(1808411648,95140971554660,95141348818735),(1808468992,95141394131070,95141771395442),(1808526336,95141812958758,95142190223424)]
theorem point_links_checked13767 : (cuts13767.take 3).map (fun c => (1808400385-1+2*2^9*c.k,95140889528135+c.lower,95141266792154+c.upper)) = pointBounds13767 := by
 decide +kernel
def cuts13768 : List PrefixCut := [⟨51,380994481,380994749⟩,
⟨107,794815434,794815992⟩,
⟨128,954021754,954022424⟩]
theorem checked13768 : checkPrefixCuts (2^48) 1808531457 9 Manual.Count131072.C013768.packed 128 cuts13768 = true := by
 decide +kernel
def pointBounds13768 : List (Nat × Nat × Nat) := [(1808583680,95142229749860,95142607014818),(1808641024,95142643570813,95143020836061)]
theorem point_links_checked13768 : (cuts13768.take 2).map (fun c => (1808531457-1+2*2^9*c.k,95141848755379+c.lower,95142226020069+c.upper)) = pointBounds13768 := by
 decide +kernel
def cuts13769 : List PrefixCut := [⟨35,263005250,263005441⟩,
⟨91,683336128,683336611⟩,
⟨128,959243889,959244568⟩]
theorem checked13769 : checkPrefixCuts (2^48) 1808662529 9 Manual.Count131072.C013769.packed 128 cuts13769 = true := by
 decide +kernel
def pointBounds13769 : List (Nat × Nat × Nat) := [(1808698368,95143065782383,95143443047934),(1808755712,95143486113261,95143863379104)]
theorem point_links_checked13769 : (cuts13769.take 2).map (fun c => (1808662529-1+2*2^9*c.k,95142802777133+c.lower,95143180042493+c.upper)) = pointBounds13769 := by
 decide +kernel
def cuts13770 : List PrefixCut := [⟨19,148766860,148766964⟩,
⟨75,577318312,577318717⟩,
⟨128,971312171,971312853⟩]
theorem checked13770 : checkPrefixCuts (2^48) 1808793601 9 Manual.Count131072.C013770.packed 128 cuts13770 = true := by
 decide +kernel
def pointBounds13770 : List (Nat × Nat × Nat) := [(1808813056,95143910787882,95144288054025),(1808870400,95144339339334,95144716605778)]
theorem point_links_checked13770 : (cuts13770.take 2).map (fun c => (1808793601-1+2*2^9*c.k,95143762021022+c.lower,95144139287061+c.upper)) = pointBounds13770 := by
 decide +kernel
def cuts13771 : List PrefixCut := [⟨3,20695238,20695252⟩,
⟨59,434904342,434904646⟩,
⟨115,844276784,844277379⟩,
⟨128,941833435,941834099⟩]
theorem checked13771 : checkPrefixCuts (2^48) 1808924673 9 Manual.Count131072.C013771.packed 128 cuts13771 = true := by
 decide +kernel
def pointBounds13771 : List (Nat × Nat × Nat) := [(1808927744,95144754028431,95145131295166),(1808985088,95145168237535,95145545504560),(1809042432,95145577609977,95145954877293)]
theorem point_links_checked13771 : (cuts13771.take 3).map (fun c => (1808924673-1+2*2^9*c.k,95144733333193+c.lower,95145110599914+c.upper)) = pointBounds13771 := by
 decide +kernel
def cuts13772 : List PrefixCut := [⟨43,323938850,323939079⟩,
⟨99,751644454,751644984⟩,
⟨128,970081822,970082505⟩]
theorem checked13772 : checkPrefixCuts (2^48) 1809055745 9 Manual.Count131072.C013772.packed 128 cuts13772 = true := by
 decide +kernel
def pointBounds13772 : List (Nat × Nat × Nat) := [(1809099776,95145999105478,95146376373092),(1809157120,95146426811082,95146804078997)]
theorem point_links_checked13772 : (cuts13772.take 2).map (fun c => (1809055745-1+2*2^9*c.k,95145675166628+c.lower,95146052434013+c.upper)) = pointBounds13772 := by
 decide +kernel
def cuts13773 : List PrefixCut := [⟨27,195096880,195097016⟩,
⟨83,618886045,618886478⟩,
⟨128,963165992,963166662⟩]
theorem checked13773 : checkPrefixCuts (2^48) 1809186817 9 Manual.Count131072.C013773.packed 128 cuts13773 = true := by
 decide +kernel
def pointBounds13773 : List (Nat × Nat × Nat) := [(1809214464,95146840345330,95147217613534),(1809271808,95147264134495,95147641402996)]
theorem point_links_checked13773 : (cuts13773.take 2).map (fun c => (1809186817-1+2*2^9*c.k,95146645248450+c.lower,95147022516518+c.upper)) = pointBounds13773 := by
 decide +kernel
def cuts13774 : List PrefixCut := [⟨11,80895943,80896000⟩,
⟨67,497035520,497035866⟩,
⟨123,915495333,915495973⟩,
⟨128,951584921,951585587⟩]
theorem checked13774 : checkPrefixCuts (2^48) 1809317889 9 Manual.Count131072.C013774.packed 128 cuts13774 = true := by
 decide +kernel
def pointBounds13774 : List (Nat × Nat × Nat) := [(1809329152,95147689310385,95148066579180),(1809386496,95148105449962,95148482719046),(1809443840,95148523909775,95148901179153)]
theorem point_links_checked13774 : (cuts13774.take 3).map (fun c => (1809317889-1+2*2^9*c.k,95147608414442+c.lower,95147985683180+c.upper)) = pointBounds13774 := by
 decide +kernel
def cuts13775 : List PrefixCut := [⟨51,384845790,384846065⟩,
⟨107,807634398,807634968⟩,
⟨128,966448897,966449577⟩]
theorem checked13775 : checkPrefixCuts (2^48) 1809448961 9 Manual.Count131072.C013775.packed 128 cuts13775 = true := by
 decide +kernel
def pointBounds13775 : List (Nat × Nat × Nat) := [(1809501184,95148944845153,95149322114832),(1809558528,95149367633761,95149744903735)]
theorem point_links_checked13775 : (cuts13775.take 2).map (fun c => (1809448961-1+2*2^9*c.k,95148559999363+c.lower,95148937268767+c.upper)) = pointBounds13775 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000117
