import PlattAssemblyKernel
import PlattCertificates.Count131072.C063776
import PlattCertificates.Count131072.C063777
import PlattCertificates.Count131072.C063778
import PlattCertificates.Count131072.C063779
import PlattCertificates.Count131072.C063780
import PlattCertificates.Count131072.C063781
import PlattCertificates.Count131072.C063782
import PlattCertificates.Count131072.C063783
import PlattCertificates.Count131072.C063784
import PlattCertificates.Count131072.C063785
import PlattCertificates.Count131072.C063786
import PlattCertificates.Count131072.C063787
import PlattCertificates.Count131072.C063788
import PlattCertificates.Count131072.C063789
import PlattCertificates.Count131072.C063790
import PlattCertificates.Count131072.C063791
import PlattCertificates.Count131072.C063792
import PlattCertificates.Count131072.C063793
import PlattCertificates.Count131072.C063794
import PlattCertificates.Count131072.C063795
import PlattCertificates.Count131072.C063796
import PlattCertificates.Count131072.C063797
import PlattCertificates.Count131072.C063798
import PlattCertificates.Count131072.C063799
import PlattCertificates.Count131072.C063800
import PlattCertificates.Count131072.C063801
import PlattCertificates.Count131072.C063802
import PlattCertificates.Count131072.C063803
import PlattCertificates.Count131072.C063804
import PlattCertificates.Count131072.C063805
import PlattCertificates.Count131072.C063806
import PlattCertificates.Count131072.C063807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63776 : List PrefixCut := [⟨48,145731538,145731622⟩,
⟨64,192345072,192345183⟩]
theorem checked63776 : checkPrefixCuts (2^48) 8363180033 10 Manual.Count131072.C063776.packed 64 cuts63776 = true := by
 decide +kernel
def pointBounds63776 : List (Nat × Nat × Nat) := [(8363278336,114669566675893,114669955514984)]
theorem point_links_checked63776 : (cuts63776.take 1).map (fun c => (8363180033-1+2*2^10*c.k,114669420944355+c.lower,114669809783362+c.upper)) = pointBounds63776 := by
 decide +kernel
def cuts63777 : List PrefixCut := [⟨64,196279762,196279871⟩]
theorem checked63777 : checkPrefixCuts (2^48) 8363311105 10 Manual.Count131072.C063777.packed 64 cuts63777 = true := by
 decide +kernel
def cuts63778 : List PrefixCut := [⟨48,143202837,143202918⟩,
⟨64,190488011,190488119⟩]
theorem checked63778 : checkPrefixCuts (2^48) 8363442177 10 Manual.Count131072.C063778.packed 64 cuts63778 = true := by
 decide +kernel
def pointBounds63778 : List (Nat × Nat × Nat) := [(8363540480,114669952772026,114670341611334)]
theorem point_links_checked63778 : (cuts63778.take 1).map (fun c => (8363442177-1+2*2^10*c.k,114669809569189+c.lower,114670198408416+c.upper)) = pointBounds63778 := by
 decide +kernel
def cuts63779 : List PrefixCut := [⟨64,195970719,195970831⟩]
theorem checked63779 : checkPrefixCuts (2^48) 8363573249 10 Manual.Count131072.C063779.packed 64 cuts63779 = true := by
 decide +kernel
def cuts63780 : List PrefixCut := [⟨48,145318565,145318647⟩,
⟨64,193982060,193982172⟩]
theorem checked63780 : checkPrefixCuts (2^48) 8363704321 10 Manual.Count131072.C063780.packed 64 cuts63780 = true := by
 decide +kernel
def pointBounds63780 : List (Nat × Nat × Nat) := [(8363802624,114670341346484,114670730186013)]
theorem point_links_checked63780 : (cuts63780.take 1).map (fun c => (8363704321-1+2*2^10*c.k,114670196027919+c.lower,114670584867366+c.upper)) = pointBounds63780 := by
 decide +kernel
def cuts63781 : List PrefixCut := [⟨64,193911713,193911822⟩]
theorem checked63781 : checkPrefixCuts (2^48) 8363835393 10 Manual.Count131072.C063781.packed 64 cuts63781 = true := by
 decide +kernel
def cuts63782 : List PrefixCut := [⟨48,144102490,144102575⟩,
⟨64,192562549,192562659⟩]
theorem checked63782 : checkPrefixCuts (2^48) 8363966465 10 Manual.Count131072.C063782.packed 64 cuts63782 = true := by
 decide +kernel
def pointBounds63782 : List (Nat × Nat × Nat) := [(8364064768,114670728024182,114671116863935)]
theorem point_links_checked63782 : (cuts63782.take 1).map (fun c => (8363966465-1+2*2^10*c.k,114670583921692+c.lower,114670972761360+c.upper)) = pointBounds63782 := by
 decide +kernel
def cuts63783 : List PrefixCut := [⟨64,194814253,194814365⟩]
theorem checked63783 : checkPrefixCuts (2^48) 8364097537 10 Manual.Count131072.C063783.packed 64 cuts63783 = true := by
 decide +kernel
def cuts63784 : List PrefixCut := [⟨48,144400835,144400910⟩,
⟨64,191311392,191311492⟩]
theorem checked63784 : checkPrefixCuts (2^48) 8364228609 10 Manual.Count131072.C063784.packed 64 cuts63784 = true := by
 decide +kernel
def pointBounds63784 : List (Nat × Nat × Nat) := [(8364326912,114671115699329,114671504539294)]
theorem point_links_checked63784 : (cuts63784.take 1).map (fun c => (8364228609-1+2*2^10*c.k,114670971298494+c.lower,114671360138384+c.upper)) = pointBounds63784 := by
 decide +kernel
def cuts63785 : List PrefixCut := [⟨64,194875442,194875560⟩]
theorem checked63785 : checkPrefixCuts (2^48) 8364359681 10 Manual.Count131072.C063785.packed 64 cuts63785 = true := by
 decide +kernel
def cuts63786 : List PrefixCut := [⟨48,147054741,147054829⟩,
⟨64,196117473,196117590⟩]
theorem checked63786 : checkPrefixCuts (2^48) 8364490753 10 Manual.Count131072.C063786.packed 64 cuts63786 = true := by
 decide +kernel
def pointBounds63786 : List (Nat × Nat × Nat) := [(8364589056,114671504540069,114671893380265)]
theorem point_links_checked63786 : (cuts63786.take 1).map (fun c => (8364490753-1+2*2^10*c.k,114671357485328+c.lower,114671746325436+c.upper)) = pointBounds63786 := by
 decide +kernel
def cuts63787 : List PrefixCut := [⟨64,192412860,192412970⟩]
theorem checked63787 : checkPrefixCuts (2^48) 8364621825 10 Manual.Count131072.C063787.packed 64 cuts63787 = true := by
 decide +kernel
def cuts63788 : List PrefixCut := [⟨48,144189898,144189976⟩,
⟨64,192880946,192881050⟩]
theorem checked63788 : checkPrefixCuts (2^48) 8364752897 10 Manual.Count131072.C063788.packed 64 cuts63788 = true := by
 decide +kernel
def pointBounds63788 : List (Nat × Nat × Nat) := [(8364851200,114671890205559,114672279045972)]
theorem point_links_checked63788 : (cuts63788.take 1).map (fun c => (8364752897-1+2*2^10*c.k,114671746015661+c.lower,114672134855996+c.upper)) = pointBounds63788 := by
 decide +kernel
def cuts63789 : List PrefixCut := [⟨64,191935744,191935855⟩]
theorem checked63789 : checkPrefixCuts (2^48) 8364883969 10 Manual.Count131072.C063789.packed 64 cuts63789 = true := by
 decide +kernel
def cuts63790 : List PrefixCut := [⟨48,145531338,145531417⟩,
⟨64,192874914,192875020⟩]
theorem checked63790 : checkPrefixCuts (2^48) 8365015041 10 Manual.Count131072.C063790.packed 64 cuts63790 = true := by
 decide +kernel
def pointBounds63790 : List (Nat × Nat × Nat) := [(8365113344,114672276363689,114672665204318)]
theorem point_links_checked63790 : (cuts63790.take 1).map (fun c => (8365015041-1+2*2^10*c.k,114672130832351+c.lower,114672519672901+c.upper)) = pointBounds63790 := by
 decide +kernel
def cuts63791 : List PrefixCut := [⟨64,195193602,195193713⟩]
theorem checked63791 : checkPrefixCuts (2^48) 8365146113 10 Manual.Count131072.C063791.packed 64 cuts63791 = true := by
 decide +kernel
def cuts63792 : List PrefixCut := [⟨48,144416393,144416474⟩,
⟨64,192969801,192969909⟩]
theorem checked63792 : checkPrefixCuts (2^48) 8365277185 10 Manual.Count131072.C063792.packed 64 cuts63792 = true := by
 decide +kernel
def pointBounds63792 : List (Nat × Nat × Nat) := [(8365375488,114672663317260,114673052158108)]
theorem point_links_checked63792 : (cuts63792.take 1).map (fun c => (8365277185-1+2*2^10*c.k,114672518900867+c.lower,114672907741634+c.upper)) = pointBounds63792 := by
 decide +kernel
def cuts63793 : List PrefixCut := [⟨64,194346319,194346425⟩]
theorem checked63793 : checkPrefixCuts (2^48) 8365408257 10 Manual.Count131072.C063793.packed 64 cuts63793 = true := by
 decide +kernel
def cuts63794 : List PrefixCut := [⟨48,146026913,146026999⟩,
⟨64,194477858,194477972⟩]
theorem checked63794 : checkPrefixCuts (2^48) 8365539329 10 Manual.Count131072.C063794.packed 64 cuts63794 = true := by
 decide +kernel
def pointBounds63794 : List (Nat × Nat × Nat) := [(8365637632,114673052243900,114673441084967)]
theorem point_links_checked63794 : (cuts63794.take 1).map (fun c => (8365539329-1+2*2^10*c.k,114672906216987+c.lower,114673295057968+c.upper)) = pointBounds63794 := by
 decide +kernel
def cuts63795 : List PrefixCut := [⟨64,191278435,191278536⟩]
theorem checked63795 : checkPrefixCuts (2^48) 8365670401 10 Manual.Count131072.C063795.packed 64 cuts63795 = true := by
 decide +kernel
def cuts63796 : List PrefixCut := [⟨48,144070867,144070947⟩,
⟨64,192082903,192083012⟩]
theorem checked63796 : checkPrefixCuts (2^48) 8365801473 10 Manual.Count131072.C063796.packed 64 cuts63796 = true := by
 decide +kernel
def pointBounds63796 : List (Nat × Nat × Nat) := [(8365899776,114673436044147,114673824885423)]
theorem point_links_checked63796 : (cuts63796.take 1).map (fun c => (8365801473-1+2*2^10*c.k,114673291973280+c.lower,114673680814476+c.upper)) = pointBounds63796 := by
 decide +kernel
def cuts63797 : List PrefixCut := [⟨64,193493011,193493126⟩]
theorem checked63797 : checkPrefixCuts (2^48) 8365932545 10 Manual.Count131072.C063797.packed 64 cuts63797 = true := by
 decide +kernel
def cuts63798 : List PrefixCut := [⟨48,145479447,145479526⟩,
⟨64,192783447,192783555⟩]
theorem checked63798 : checkPrefixCuts (2^48) 8366063617 10 Manual.Count131072.C063798.packed 64 cuts63798 = true := by
 decide +kernel
def pointBounds63798 : List (Nat × Nat × Nat) := [(8366161920,114673823028641,114674211870140)]
theorem point_links_checked63798 : (cuts63798.take 1).map (fun c => (8366063617-1+2*2^10*c.k,114673677549194+c.lower,114674066390614+c.upper)) = pointBounds63798 := by
 decide +kernel
def cuts63799 : List PrefixCut := [⟨64,194092536,194092651⟩]
theorem checked63799 : checkPrefixCuts (2^48) 8366194689 10 Manual.Count131072.C063799.packed 64 cuts63799 = true := by
 decide +kernel
def cuts63800 : List PrefixCut := [⟨48,146080471,146080553⟩,
⟨64,195233373,195233483⟩]
theorem checked63800 : checkPrefixCuts (2^48) 8366325761 10 Manual.Count131072.C063800.packed 64 cuts63800 = true := by
 decide +kernel
def pointBounds63800 : List (Nat × Nat × Nat) := [(8366424064,114674210505648,114674599347373)]
theorem point_links_checked63800 : (cuts63800.take 1).map (fun c => (8366325761-1+2*2^10*c.k,114674064425177+c.lower,114674453266820+c.upper)) = pointBounds63800 := by
 decide +kernel
def cuts63801 : List PrefixCut := [⟨64,195970472,195970587⟩]
theorem checked63801 : checkPrefixCuts (2^48) 8366456833 10 Manual.Count131072.C063801.packed 64 cuts63801 = true := by
 decide +kernel
def cuts63802 : List PrefixCut := [⟨48,145874041,145874127⟩,
⟨64,192872298,192872410⟩]
theorem checked63802 : checkPrefixCuts (2^48) 8366587905 10 Manual.Count131072.C063802.packed 64 cuts63802 = true := by
 decide +kernel
def pointBounds63802 : List (Nat × Nat × Nat) := [(8366686208,114674601503063,114674990345017)]
theorem point_links_checked63802 : (cuts63802.take 1).map (fun c => (8366587905-1+2*2^10*c.k,114674455629022+c.lower,114674844470890+c.upper)) = pointBounds63802 := by
 decide +kernel
def cuts63803 : List PrefixCut := [⟨64,192701060,192701172⟩]
theorem checked63803 : checkPrefixCuts (2^48) 8366718977 10 Manual.Count131072.C063803.packed 64 cuts63803 = true := by
 decide +kernel
def cuts63804 : List PrefixCut := [⟨48,144759290,144759374⟩,
⟨64,193101723,193101832⟩]
theorem checked63804 : checkPrefixCuts (2^48) 8366850049 10 Manual.Count131072.C063804.packed 64 cuts63804 = true := by
 decide +kernel
def pointBounds63804 : List (Nat × Nat × Nat) := [(8366948352,114674985961670,114675374803846)]
theorem point_links_checked63804 : (cuts63804.take 1).map (fun c => (8366850049-1+2*2^10*c.k,114674841202380+c.lower,114675230044472+c.upper)) = pointBounds63804 := by
 decide +kernel
def cuts63805 : List PrefixCut := [⟨64,193468770,193468881⟩]
theorem checked63805 : checkPrefixCuts (2^48) 8366981121 10 Manual.Count131072.C063805.packed 64 cuts63805 = true := by
 decide +kernel
def cuts63806 : List PrefixCut := [⟨48,146234947,146235029⟩,
⟨64,195753269,195753380⟩]
theorem checked63806 : checkPrefixCuts (2^48) 8367112193 10 Manual.Count131072.C063806.packed 64 cuts63806 = true := by
 decide +kernel
def pointBounds63806 : List (Nat × Nat × Nat) := [(8367210496,114675374007820,114675762850214)]
theorem point_links_checked63806 : (cuts63806.take 1).map (fun c => (8367112193-1+2*2^10*c.k,114675227772873+c.lower,114675616615185+c.upper)) = pointBounds63806 := by
 decide +kernel
def cuts63807 : List PrefixCut := [⟨64,189156798,189156909⟩]
theorem checked63807 : checkPrefixCuts (2^48) 8367243265 10 Manual.Count131072.C063807.packed 64 cuts63807 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000118
