import PlattAssemblyKernel
import PlattCertificates.Count131072.C039760
import PlattCertificates.Count131072.C039761
import PlattCertificates.Count131072.C039762
import PlattCertificates.Count131072.C039763
import PlattCertificates.Count131072.C039764
import PlattCertificates.Count131072.C039765
import PlattCertificates.Count131072.C039766
import PlattCertificates.Count131072.C039767
import PlattCertificates.Count131072.C039768
import PlattCertificates.Count131072.C039769
import PlattCertificates.Count131072.C039770
import PlattCertificates.Count131072.C039771
import PlattCertificates.Count131072.C039772
import PlattCertificates.Count131072.C039773
import PlattCertificates.Count131072.C039774
import PlattCertificates.Count131072.C039775
import PlattCertificates.Count131072.C039776
import PlattCertificates.Count131072.C039777
import PlattCertificates.Count131072.C039778
import PlattCertificates.Count131072.C039779
import PlattCertificates.Count131072.C039780
import PlattCertificates.Count131072.C039781
import PlattCertificates.Count131072.C039782
import PlattCertificates.Count131072.C039783
import PlattCertificates.Count131072.C039784
import PlattCertificates.Count131072.C039785
import PlattCertificates.Count131072.C039786
import PlattCertificates.Count131072.C039787
import PlattCertificates.Count131072.C039788
import PlattCertificates.Count131072.C039789
import PlattCertificates.Count131072.C039790
import PlattCertificates.Count131072.C039791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000305
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39760 : List PrefixCut := [⟨4,20616685,20616697⟩,
⟨64,316478589,316478775⟩]
theorem checked39760 : checkPrefixCuts (2^48) 5215354881 10 Manual.Count131072.C039760.packed 64 cuts39760 = true := by
 decide +kernel
def pointBounds39760 : List (Nat × Nat × Nat) := [(5215363072,108790619001178,108791004461885)]
theorem point_links_checked39760 : (cuts39760.take 1).map (fun c => (5215354881-1+2*2^10*c.k,108790598384493+c.lower,108790983845188+c.upper)) = pointBounds39760 := by
 decide +kernel
def cuts39761 : List PrefixCut := [⟨20,102163036,102163096⟩,
⟨64,320464290,320464483⟩]
theorem checked39761 : checkPrefixCuts (2^48) 5215485953 10 Manual.Count131072.C039761.packed 64 cuts39761 = true := by
 decide +kernel
def pointBounds39761 : List (Nat × Nat × Nat) := [(5215526912,108791017026118,108791402487059)]
theorem point_links_checked39761 : (cuts39761.take 1).map (fun c => (5215485953-1+2*2^10*c.k,108790914863082+c.lower,108791300323963+c.upper)) = pointBounds39761 := by
 decide +kernel
def cuts39762 : List PrefixCut := [⟨36,181168313,181168420⟩,
⟨64,320240362,320240553⟩]
theorem checked39762 : checkPrefixCuts (2^48) 5215617025 10 Manual.Count131072.C039762.packed 64 cuts39762 = true := by
 decide +kernel
def pointBounds39762 : List (Nat × Nat × Nat) := [(5215690752,108791416495685,108791801956866)]
theorem point_links_checked39762 : (cuts39762.take 1).map (fun c => (5215617025-1+2*2^10*c.k,108791235327372+c.lower,108791620788446+c.upper)) = pointBounds39762 := by
 decide +kernel
def cuts39763 : List PrefixCut := [⟨52,254502708,254502857⟩,
⟨64,311435912,311436096⟩]
theorem checked39763 : checkPrefixCuts (2^48) 5215748097 10 Manual.Count131072.C039763.packed 64 cuts39763 = true := by
 decide +kernel
def pointBounds39763 : List (Nat × Nat × Nat) := [(5215854592,108791810070442,108792195531856)]
theorem point_links_checked39763 : (cuts39763.take 1).map (fun c => (5215748097-1+2*2^10*c.k,108791555567734+c.lower,108791941028999+c.upper)) = pointBounds39763 := by
 decide +kernel
def cuts39764 : List PrefixCut := [⟨64,314719866,314720059⟩]
theorem checked39764 : checkPrefixCuts (2^48) 5215879169 10 Manual.Count131072.C039764.packed 64 cuts39764 = true := by
 decide +kernel
def cuts39765 : List PrefixCut := [⟨4,19804641,19804651⟩,
⟨64,315305563,315305752⟩]
theorem checked39765 : checkPrefixCuts (2^48) 5216010241 10 Manual.Count131072.C039765.packed 64 cuts39765 = true := by
 decide +kernel
def pointBounds39765 : List (Nat × Nat × Nat) := [(5216018432,108792201528153,108792586989805)]
theorem point_links_checked39765 : (cuts39765.take 1).map (fun c => (5216010241-1+2*2^10*c.k,108792181723512+c.lower,108792567185154+c.upper)) = pointBounds39765 := by
 decide +kernel
def cuts39766 : List PrefixCut := [⟨20,96052491,96052548⟩,
⟨64,312329737,312329921⟩]
theorem checked39766 : checkPrefixCuts (2^48) 5216141313 10 Manual.Count131072.C039766.packed 64 cuts39766 = true := by
 decide +kernel
def pointBounds39766 : List (Nat × Nat × Nat) := [(5216182272,108792593081566,108792978543454)]
theorem point_links_checked39766 : (cuts39766.take 1).map (fun c => (5216141313-1+2*2^10*c.k,108792497029075+c.lower,108792882490906+c.upper)) = pointBounds39766 := by
 decide +kernel
def cuts39767 : List PrefixCut := [⟨36,175317836,175317938⟩,
⟨64,316314972,316315155⟩]
theorem checked39767 : checkPrefixCuts (2^48) 5216272385 10 Manual.Count131072.C039767.packed 64 cuts39767 = true := by
 decide +kernel
def pointBounds39767 : List (Nat × Nat × Nat) := [(5216346112,108792984676648,108793370138765)]
theorem point_links_checked39767 : (cuts39767.take 1).map (fun c => (5216272385-1+2*2^10*c.k,108792809358812+c.lower,108793194820827+c.upper)) = pointBounds39767 := by
 decide +kernel
def cuts39768 : List PrefixCut := [⟨52,257708268,257708419⟩,
⟨64,316091194,316091378⟩]
theorem checked39768 : checkPrefixCuts (2^48) 5216403457 10 Manual.Count131072.C039768.packed 64 cuts39768 = true := by
 decide +kernel
def pointBounds39768 : List (Nat × Nat × Nat) := [(5216509952,108793383382052,108793768844401)]
theorem point_links_checked39768 : (cuts39768.take 1).map (fun c => (5216403457-1+2*2^10*c.k,108793125673784+c.lower,108793511135982+c.upper)) = pointBounds39768 := by
 decide +kernel
def cuts39769 : List PrefixCut := [⟨64,316730739,316730925⟩]
theorem checked39769 : checkPrefixCuts (2^48) 5216534529 10 Manual.Count131072.C039769.packed 64 cuts39769 = true := by
 decide +kernel
def cuts39770 : List PrefixCut := [⟨4,20179850,20179862⟩,
⟨64,317100517,317100709⟩]
theorem checked39770 : checkPrefixCuts (2^48) 5216665601 10 Manual.Count131072.C039770.packed 64 cuts39770 = true := by
 decide +kernel
def pointBounds39770 : List (Nat × Nat × Nat) := [(5216673792,108793778675567,108794164138147)]
theorem point_links_checked39770 : (cuts39770.take 1).map (fun c => (5216665601-1+2*2^10*c.k,108793758495717+c.lower,108794143958285+c.upper)) = pointBounds39770 := by
 decide +kernel
def cuts39771 : List PrefixCut := [⟨20,97227435,97227495⟩,
⟨64,309862563,309862750⟩]
theorem checked39771 : checkPrefixCuts (2^48) 5216796673 10 Manual.Count131072.C039771.packed 64 cuts39771 = true := by
 decide +kernel
def pointBounds39771 : List (Nat × Nat × Nat) := [(5216837632,108794172823669,108794558286489)]
theorem point_links_checked39771 : (cuts39771.take 1).map (fun c => (5216796673-1+2*2^10*c.k,108794075596234+c.lower,108794461058994+c.upper)) = pointBounds39771 := by
 decide +kernel
def cuts39772 : List PrefixCut := [⟨36,173677186,173677290⟩,
⟨64,312552433,312552618⟩]
theorem checked39772 : checkPrefixCuts (2^48) 5216927745 10 Manual.Count131072.C039772.packed 64 cuts39772 = true := by
 decide +kernel
def pointBounds39772 : List (Nat × Nat × Nat) := [(5217001472,108794559135983,108794944599034)]
theorem point_links_checked39772 : (cuts39772.take 1).map (fun c => (5216927745-1+2*2^10*c.k,108794385458797+c.lower,108794770921744+c.upper)) = pointBounds39772 := by
 decide +kernel
def cuts39773 : List PrefixCut := [⟨52,254924337,254924488⟩,
⟨64,313407832,313408018⟩]
theorem checked39773 : checkPrefixCuts (2^48) 5217058817 10 Manual.Count131072.C039773.packed 64 cuts39773 = true := by
 decide +kernel
def pointBounds39773 : List (Nat × Nat × Nat) := [(5217165312,108794952935567,108795338398850)]
theorem point_links_checked39773 : (cuts39773.take 1).map (fun c => (5217058817-1+2*2^10*c.k,108794698011230+c.lower,108795083474362+c.upper)) = pointBounds39773 := by
 decide +kernel
def cuts39774 : List PrefixCut := [⟨64,325107290,325107480⟩]
theorem checked39774 : checkPrefixCuts (2^48) 5217189889 10 Manual.Count131072.C039774.packed 64 cuts39774 = true := by
 decide +kernel
def cuts39775 : List PrefixCut := [⟨4,19206214,19206225⟩,
⟨64,318031732,318031920⟩]
theorem checked39775 : checkPrefixCuts (2^48) 5217320961 10 Manual.Count131072.C039775.packed 64 cuts39775 = true := by
 decide +kernel
def pointBounds39775 : List (Nat × Nat × Nat) := [(5217329152,108795355732566,108795741196085)]
theorem point_links_checked39775 : (cuts39775.take 1).map (fun c => (5217320961-1+2*2^10*c.k,108795336526352+c.lower,108795721989860+c.upper)) = pointBounds39775 := by
 decide +kernel
def cuts39776 : List PrefixCut := [⟨20,98132347,98132405⟩,
⟨64,311280224,311280402⟩]
theorem checked39776 : checkPrefixCuts (2^48) 5217452033 10 Manual.Count131072.C039776.packed 64 cuts39776 = true := by
 decide +kernel
def pointBounds39776 : List (Nat × Nat × Nat) := [(5217492992,108795752690431,108796138154185)]
theorem point_links_checked39776 : (cuts39776.take 1).map (fun c => (5217452033-1+2*2^10*c.k,108795654558084+c.lower,108796040021780+c.upper)) = pointBounds39776 := by
 decide +kernel
def cuts39777 : List PrefixCut := [⟨36,176622446,176622551⟩,
⟨64,314832894,314833080⟩]
theorem checked39777 : checkPrefixCuts (2^48) 5217583105 10 Manual.Count131072.C039777.packed 64 cuts39777 = true := by
 decide +kernel
def pointBounds39777 : List (Nat × Nat × Nat) := [(5217656832,108796142460754,108796527924733)]
theorem point_links_checked39777 : (cuts39777.take 1).map (fun c => (5217583105-1+2*2^10*c.k,108795965838308+c.lower,108796351302182+c.upper)) = pointBounds39777 := by
 decide +kernel
def cuts39778 : List PrefixCut := [⟨52,259963173,259963325⟩,
⟨64,319410329,319410516⟩]
theorem checked39778 : checkPrefixCuts (2^48) 5217714177 10 Manual.Count131072.C039778.packed 64 cuts39778 = true := by
 decide +kernel
def pointBounds39778 : List (Nat × Nat × Nat) := [(5217820672,108796540634375,108796926098587)]
theorem point_links_checked39778 : (cuts39778.take 1).map (fun c => (5217714177-1+2*2^10*c.k,108796280671202+c.lower,108796666135262+c.upper)) = pointBounds39778 := by
 decide +kernel
def cuts39779 : List PrefixCut := [⟨64,315032831,315033018⟩]
theorem checked39779 : checkPrefixCuts (2^48) 5217845249 10 Manual.Count131072.C039779.packed 64 cuts39779 = true := by
 decide +kernel
def cuts39780 : List PrefixCut := [⟨4,19959007,19959019⟩,
⟨64,317236615,317236804⟩]
theorem checked39780 : checkPrefixCuts (2^48) 5217976321 10 Manual.Count131072.C039780.packed 64 cuts39780 = true := by
 decide +kernel
def pointBounds39780 : List (Nat × Nat × Nat) := [(5217984512,108796935073369,108797320537815)]
theorem point_links_checked39780 : (cuts39780.take 1).map (fun c => (5217976321-1+2*2^10*c.k,108796915114362+c.lower,108797300578796+c.upper)) = pointBounds39780 := by
 decide +kernel
def cuts39781 : List PrefixCut := [⟨20,100385569,100385629⟩,
⟨64,320842681,320842873⟩]
theorem checked39781 : checkPrefixCuts (2^48) 5218107393 10 Manual.Count131072.C039781.packed 64 cuts39781 = true := by
 decide +kernel
def pointBounds39781 : List (Nat × Nat × Nat) := [(5218148352,108797332736546,108797718201229)]
theorem point_links_checked39781 : (cuts39781.take 1).map (fun c => (5218107393-1+2*2^10*c.k,108797232350977+c.lower,108797617815600+c.upper)) = pointBounds39781 := by
 decide +kernel
def cuts39782 : List PrefixCut := [⟨36,179513028,179513137⟩,
⟨64,321374001,321374195⟩]
theorem checked39782 : checkPrefixCuts (2^48) 5218238465 10 Manual.Count131072.C039782.packed 64 cuts39782 = true := by
 decide +kernel
def pointBounds39782 : List (Nat × Nat × Nat) := [(5218312192,108797732706686,108798118171610)]
theorem point_links_checked39782 : (cuts39782.take 1).map (fun c => (5218238465-1+2*2^10*c.k,108797553193658+c.lower,108797938658473+c.upper)) = pointBounds39782 := by
 decide +kernel
def cuts39783 : List PrefixCut := [⟨52,252379118,252379273⟩,
⟨64,310470356,310470546⟩]
theorem checked39783 : checkPrefixCuts (2^48) 5218369537 10 Manual.Count131072.C039783.packed 64 cuts39783 = true := by
 decide +kernel
def pointBounds39783 : List (Nat × Nat × Nat) := [(5218476032,108798126946777,108798512411941)]
theorem point_links_checked39783 : (cuts39783.take 1).map (fun c => (5218369537-1+2*2^10*c.k,108797874567659+c.lower,108798260032668+c.upper)) = pointBounds39783 := by
 decide +kernel
def cuts39784 : List PrefixCut := [⟨64,314615717,314615903⟩]
theorem checked39784 : checkPrefixCuts (2^48) 5218500609 10 Manual.Count131072.C039784.packed 64 cuts39784 = true := by
 decide +kernel
def cuts39785 : List PrefixCut := [⟨4,19686819,19686830⟩,
⟨64,316927051,316927237⟩]
theorem checked39785 : checkPrefixCuts (2^48) 5218631681 10 Manual.Count131072.C039785.packed 64 cuts39785 = true := by
 decide +kernel
def pointBounds39785 : List (Nat × Nat × Nat) := [(5218639872,108798519340551,108798904805947)]
theorem point_links_checked39785 : (cuts39785.take 1).map (fun c => (5218631681-1+2*2^10*c.k,108798499653732+c.lower,108798885119117+c.upper)) = pointBounds39785 := by
 decide +kernel
def cuts39786 : List PrefixCut := [⟨20,97136870,97136929⟩,
⟨64,313251546,313251733⟩]
theorem checked39786 : checkPrefixCuts (2^48) 5218762753 10 Manual.Count131072.C039786.packed 64 cuts39786 = true := by
 decide +kernel
def pointBounds39786 : List (Nat × Nat × Nat) := [(5218803712,108798913717653,108799299183283)]
theorem point_links_checked39786 : (cuts39786.take 1).map (fun c => (5218762753-1+2*2^10*c.k,108798816580783+c.lower,108799202046354+c.upper)) = pointBounds39786 := by
 decide +kernel
def cuts39787 : List PrefixCut := [⟨36,176901690,176901797⟩,
⟨64,316695419,316695610⟩]
theorem checked39787 : checkPrefixCuts (2^48) 5218893825 10 Manual.Count131072.C039787.packed 64 cuts39787 = true := by
 decide +kernel
def pointBounds39787 : List (Nat × Nat × Nat) := [(5218967552,108799306734019,108799692199884)]
theorem point_links_checked39787 : (cuts39787.take 1).map (fun c => (5218893825-1+2*2^10*c.k,108799129832329+c.lower,108799515298087+c.upper)) = pointBounds39787 := by
 decide +kernel
def cuts39788 : List PrefixCut := [⟨52,257686672,257686826⟩,
⟨64,315932413,315932603⟩]
theorem checked39788 : checkPrefixCuts (2^48) 5219024897 10 Manual.Count131072.C039788.packed 64 cuts39788 = true := by
 decide +kernel
def pointBounds39788 : List (Nat × Nat × Nat) := [(5219131392,108799704214420,108800089680523)]
theorem point_links_checked39788 : (cuts39788.take 1).map (fun c => (5219024897-1+2*2^10*c.k,108799446527748+c.lower,108799831993697+c.upper)) = pointBounds39788 := by
 decide +kernel
def cuts39789 : List PrefixCut := [⟨64,317380636,317380825⟩]
theorem checked39789 : checkPrefixCuts (2^48) 5219155969 10 Manual.Count131072.C039789.packed 64 cuts39789 = true := by
 decide +kernel
def cuts39790 : List PrefixCut := [⟨4,18282173,18282185⟩,
⟨64,312411177,312411363⟩]
theorem checked39790 : checkPrefixCuts (2^48) 5219287041 10 Manual.Count131072.C039790.packed 64 cuts39790 = true := by
 decide +kernel
def pointBounds39790 : List (Nat × Nat × Nat) := [(5219295232,108800098122970,108800483589310)]
theorem point_links_checked39790 : (cuts39790.take 1).map (fun c => (5219287041-1+2*2^10*c.k,108800079840797+c.lower,108800465307125+c.upper)) = pointBounds39790 := by
 decide +kernel
def cuts39791 : List PrefixCut := [⟨20,96585390,96585448⟩,
⟨64,313158291,313158473⟩]
theorem checked39791 : checkPrefixCuts (2^48) 5219418113 10 Manual.Count131072.C039791.packed 64 cuts39791 = true := by
 decide +kernel
def pointBounds39791 : List (Nat × Nat × Nat) := [(5219459072,108800488837364,108800874303936)]
theorem point_links_checked39791 : (cuts39791.take 1).map (fun c => (5219418113-1+2*2^10*c.k,108800392251974+c.lower,108800777718488+c.upper)) = pointBounds39791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000305
