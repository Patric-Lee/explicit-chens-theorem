import PlattAssemblyKernel
import PlattCertificates.Count131072.C071632
import PlattCertificates.Count131072.C071633
import PlattCertificates.Count131072.C071634
import PlattCertificates.Count131072.C071635
import PlattCertificates.Count131072.C071636
import PlattCertificates.Count131072.C071637
import PlattCertificates.Count131072.C071638
import PlattCertificates.Count131072.C071639
import PlattCertificates.Count131072.C071640
import PlattCertificates.Count131072.C071641
import PlattCertificates.Count131072.C071642
import PlattCertificates.Count131072.C071643
import PlattCertificates.Count131072.C071644
import PlattCertificates.Count131072.C071645
import PlattCertificates.Count131072.C071646
import PlattCertificates.Count131072.C071647
import PlattCertificates.Count131072.C071648
import PlattCertificates.Count131072.C071649
import PlattCertificates.Count131072.C071650
import PlattCertificates.Count131072.C071651
import PlattCertificates.Count131072.C071652
import PlattCertificates.Count131072.C071653
import PlattCertificates.Count131072.C071654
import PlattCertificates.Count131072.C071655
import PlattCertificates.Count131072.C071656
import PlattCertificates.Count131072.C071657
import PlattCertificates.Count131072.C071658
import PlattCertificates.Count131072.C071659
import PlattCertificates.Count131072.C071660
import PlattCertificates.Count131072.C071661
import PlattCertificates.Count131072.C071662
import PlattCertificates.Count131072.C071663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71632 : List PrefixCut := [⟨46,123402783,123402852⟩,
⟨64,171169338,171169436⟩]
theorem checked71632 : checkPrefixCuts (2^48) 9392881665 10 Manual.Count131072.C071632.packed 64 cuts71632 = true := by
 decide +kernel
def pointBounds71632 : List (Nat × Nat × Nat) := [(9392975872,116096390928034,116096780600078)]
theorem point_links_checked71632 : (cuts71632.take 1).map (fun c => (9392881665-1+2*2^10*c.k,116096267525251+c.lower,116096657197226+c.upper)) = pointBounds71632 := by
 decide +kernel
def cuts71633 : List PrefixCut := [⟨64,170477735,170477839⟩]
theorem checked71633 : checkPrefixCuts (2^48) 9393012737 10 Manual.Count131072.C071633.packed 64 cuts71633 = true := by
 decide +kernel
def cuts71634 : List PrefixCut := [⟨62,166729670,166729769⟩,
⟨64,171853785,171853887⟩]
theorem checked71634 : checkPrefixCuts (2^48) 9393143809 10 Manual.Count131072.C071634.packed 64 cuts71634 = true := by
 decide +kernel
def pointBounds71634 : List (Nat × Nat × Nat) := [(9393270784,116096775901994,116097165574270)]
theorem point_links_checked71634 : (cuts71634.take 1).map (fun c => (9393143809-1+2*2^10*c.k,116096609172324+c.lower,116096998844501+c.upper)) = pointBounds71634 := by
 decide +kernel
def cuts71635 : List PrefixCut := [⟨64,173319686,173319789⟩]
theorem checked71635 : checkPrefixCuts (2^48) 9393274881 10 Manual.Count131072.C071635.packed 64 cuts71635 = true := by
 decide +kernel
def cuts71636 : List PrefixCut := [⟨64,174186253,174186355⟩]
theorem checked71636 : checkPrefixCuts (2^48) 9393405953 10 Manual.Count131072.C071636.packed 64 cuts71636 = true := by
 decide +kernel
def cuts71637 : List PrefixCut := [⟨14,37306044,37306066⟩,
⟨64,169749068,169749169⟩]
theorem checked71637 : checkPrefixCuts (2^48) 9393537025 10 Manual.Count131072.C071637.packed 64 cuts71637 = true := by
 decide +kernel
def pointBounds71637 : List (Nat × Nat × Nat) := [(9393565696,116097165838092,116097555510598)]
theorem point_links_checked71637 : (cuts71637.take 1).map (fun c => (9393537025-1+2*2^10*c.k,116097128532048+c.lower,116097518204532+c.upper)) = pointBounds71637 := by
 decide +kernel
def cuts71638 : List PrefixCut := [⟨64,172323614,172323719⟩]
theorem checked71638 : checkPrefixCuts (2^48) 9393668097 10 Manual.Count131072.C071638.packed 64 cuts71638 = true := by
 decide +kernel
def cuts71639 : List PrefixCut := [⟨30,79613831,79613878⟩,
⟨64,169115096,169115198⟩]
theorem checked71639 : checkPrefixCuts (2^48) 9393799169 10 Manual.Count131072.C071639.packed 64 cuts71639 = true := by
 decide +kernel
def pointBounds71639 : List (Nat × Nat × Nat) := [(9393860608,116097550218561,116097939891298)]
theorem point_links_checked71639 : (cuts71639.take 1).map (fun c => (9393799169-1+2*2^10*c.k,116097470604730+c.lower,116097860277420+c.upper)) = pointBounds71639 := by
 decide +kernel
def cuts71640 : List PrefixCut := [⟨64,168992882,168992980⟩]
theorem checked71640 : checkPrefixCuts (2^48) 9393930241 10 Manual.Count131072.C071640.packed 64 cuts71640 = true := by
 decide +kernel
def cuts71641 : List PrefixCut := [⟨46,123896660,123896731⟩,
⟨64,172765837,172765935⟩]
theorem checked71641 : checkPrefixCuts (2^48) 9394061313 10 Manual.Count131072.C071641.packed 64 cuts71641 = true := by
 decide +kernel
def pointBounds71641 : List (Nat × Nat × Nat) := [(9394155520,116097932609368,116098322282329)]
theorem point_links_checked71641 : (cuts71641.take 1).map (fun c => (9394061313-1+2*2^10*c.k,116097808712708+c.lower,116098198385598+c.upper)) = pointBounds71641 := by
 decide +kernel
def cuts71642 : List PrefixCut := [⟨64,174681027,174681138⟩]
theorem checked71642 : checkPrefixCuts (2^48) 9394192385 10 Manual.Count131072.C071642.packed 64 cuts71642 = true := by
 decide +kernel
def cuts71643 : List PrefixCut := [⟨62,167128197,167128305⟩,
⟨64,172401477,172401589⟩]
theorem checked71643 : checkPrefixCuts (2^48) 9394323457 10 Manual.Count131072.C071643.packed 64 cuts71643 = true := by
 decide +kernel
def pointBounds71643 : List (Nat × Nat × Nat) := [(9394450432,116098323287769,116098712960976)]
theorem point_links_checked71643 : (cuts71643.take 1).map (fun c => (9394323457-1+2*2^10*c.k,116098156159572+c.lower,116098545832671+c.upper)) = pointBounds71643 := by
 decide +kernel
def cuts71644 : List PrefixCut := [⟨64,172159385,172159491⟩]
theorem checked71644 : checkPrefixCuts (2^48) 9394454529 10 Manual.Count131072.C071644.packed 64 cuts71644 = true := by
 decide +kernel
def cuts71645 : List PrefixCut := [⟨64,169220780,169220882⟩]
theorem checked71645 : checkPrefixCuts (2^48) 9394585601 10 Manual.Count131072.C071645.packed 64 cuts71645 = true := by
 decide +kernel
def cuts71646 : List PrefixCut := [⟨14,37511084,37511110⟩,
⟨64,171285717,171285821⟩]
theorem checked71646 : checkPrefixCuts (2^48) 9394716673 10 Manual.Count131072.C071646.packed 64 cuts71646 = true := by
 decide +kernel
def pointBounds71646 : List (Nat × Nat × Nat) := [(9394745344,116098707452298,116099097125743)]
theorem point_links_checked71646 : (cuts71646.take 1).map (fun c => (9394716673-1+2*2^10*c.k,116098669941214+c.lower,116099059614633+c.upper)) = pointBounds71646 := by
 decide +kernel
def cuts71647 : List PrefixCut := [⟨64,171463093,171463193⟩]
theorem checked71647 : checkPrefixCuts (2^48) 9394847745 10 Manual.Count131072.C071647.packed 64 cuts71647 = true := by
 decide +kernel
def cuts71648 : List PrefixCut := [⟨30,78285593,78285642⟩,
⟨64,168554568,168554675⟩]
theorem checked71648 : checkPrefixCuts (2^48) 9394978817 10 Manual.Count131072.C071648.packed 64 cuts71648 = true := by
 decide +kernel
def pointBounds71648 : List (Nat × Nat × Nat) := [(9395040256,116099090975617,116099480649289)]
theorem point_links_checked71648 : (cuts71648.take 1).map (fun c => (9394978817-1+2*2^10*c.k,116099012690024+c.lower,116099402363647+c.upper)) = pointBounds71648 := by
 decide +kernel
def cuts71649 : List PrefixCut := [⟨64,172656683,172656788⟩]
theorem checked71649 : checkPrefixCuts (2^48) 9395109889 10 Manual.Count131072.C071649.packed 64 cuts71649 = true := by
 decide +kernel
def cuts71650 : List PrefixCut := [⟨46,123281922,123281997⟩,
⟨64,171695581,171695685⟩]
theorem checked71650 : checkPrefixCuts (2^48) 9395240961 10 Manual.Count131072.C071650.packed 64 cuts71650 = true := by
 decide +kernel
def pointBounds71650 : List (Nat × Nat × Nat) := [(9395335168,116099477183197,116099866857107)]
theorem point_links_checked71650 : (cuts71650.take 1).map (fun c => (9395240961-1+2*2^10*c.k,116099353901275+c.lower,116099743575110+c.upper)) = pointBounds71650 := by
 decide +kernel
def cuts71651 : List PrefixCut := [⟨64,168907034,168907142⟩]
theorem checked71651 : checkPrefixCuts (2^48) 9395372033 10 Manual.Count131072.C071651.packed 64 cuts71651 = true := by
 decide +kernel
def cuts71652 : List PrefixCut := [⟨62,164950230,164950325⟩,
⟨64,170492471,170492569⟩]
theorem checked71652 : checkPrefixCuts (2^48) 9395503105 10 Manual.Count131072.C071652.packed 64 cuts71652 = true := by
 decide +kernel
def pointBounds71652 : List (Nat × Nat × Nat) := [(9395630080,116099859454120,116100249128262)]
theorem point_links_checked71652 : (cuts71652.take 1).map (fun c => (9395503105-1+2*2^10*c.k,116099694503890+c.lower,116100084177937+c.upper)) = pointBounds71652 := by
 decide +kernel
def cuts71653 : List PrefixCut := [⟨64,170999358,170999459⟩]
theorem checked71653 : checkPrefixCuts (2^48) 9395634177 10 Manual.Count131072.C071653.packed 64 cuts71653 = true := by
 decide +kernel
def cuts71654 : List PrefixCut := [⟨64,171206689,171206785⟩]
theorem checked71654 : checkPrefixCuts (2^48) 9395765249 10 Manual.Count131072.C071654.packed 64 cuts71654 = true := by
 decide +kernel
def cuts71655 : List PrefixCut := [⟨14,38195393,38195413⟩,
⟨64,171414002,171414103⟩]
theorem checked71655 : checkPrefixCuts (2^48) 9395896321 10 Manual.Count131072.C071655.packed 64 cuts71655 = true := by
 decide +kernel
def pointBounds71655 : List (Nat × Nat × Nat) := [(9395924992,116100245397801,116100635072163)]
theorem point_links_checked71655 : (cuts71655.take 1).map (fun c => (9395896321-1+2*2^10*c.k,116100207202408+c.lower,116100596876750+c.upper)) = pointBounds71655 := by
 decide +kernel
def cuts71656 : List PrefixCut := [⟨64,172010741,172010839⟩]
theorem checked71656 : checkPrefixCuts (2^48) 9396027393 10 Manual.Count131072.C071656.packed 64 cuts71656 = true := by
 decide +kernel
def cuts71657 : List PrefixCut := [⟨30,81421174,81421220⟩,
⟨64,172307898,172308000⟩]
theorem checked71657 : checkPrefixCuts (2^48) 9396158465 10 Manual.Count131072.C071657.packed 64 cuts71657 = true := by
 decide +kernel
def pointBounds71657 : List (Nat × Nat × Nat) := [(9396219904,116100632048325,116101021722912)]
theorem point_links_checked71657 : (cuts71657.take 1).map (fun c => (9396158465-1+2*2^10*c.k,116100550627151+c.lower,116100940301692+c.upper)) = pointBounds71657 := by
 decide +kernel
def cuts71658 : List PrefixCut := [⟨64,171197125,171197220⟩]
theorem checked71658 : checkPrefixCuts (2^48) 9396289537 10 Manual.Count131072.C071658.packed 64 cuts71658 = true := by
 decide +kernel
def cuts71659 : List PrefixCut := [⟨46,121499072,121499148⟩,
⟨64,169696965,169697069⟩]
theorem checked71659 : checkPrefixCuts (2^48) 9396420609 10 Manual.Count131072.C071659.packed 64 cuts71659 = true := by
 decide +kernel
def pointBounds71659 : List (Nat × Nat × Nat) := [(9396514816,116101015631246,116101405306060)]
theorem point_links_checked71659 : (cuts71659.take 1).map (fun c => (9396420609-1+2*2^10*c.k,116100894132174+c.lower,116101283806912+c.upper)) = pointBounds71659 := by
 decide +kernel
def cuts71660 : List PrefixCut := [⟨64,171461949,171462047⟩]
theorem checked71660 : checkPrefixCuts (2^48) 9396551681 10 Manual.Count131072.C071660.packed 64 cuts71660 = true := by
 decide +kernel
def cuts71661 : List PrefixCut := [⟨62,164629967,164630062⟩,
⟨64,169961832,169961931⟩]
theorem checked71661 : checkPrefixCuts (2^48) 9396682753 10 Manual.Count131072.C071661.packed 64 cuts71661 = true := by
 decide +kernel
def pointBounds71661 : List (Nat × Nat × Nat) := [(9396809728,116101399921055,116101789596090)]
theorem point_links_checked71661 : (cuts71661.take 1).map (fun c => (9396682753-1+2*2^10*c.k,116101235291088+c.lower,116101624966028+c.upper)) = pointBounds71661 := by
 decide +kernel
def cuts71662 : List PrefixCut := [⟨64,173523999,173524098⟩]
theorem checked71662 : checkPrefixCuts (2^48) 9396813825 10 Manual.Count131072.C071662.packed 64 cuts71662 = true := by
 decide +kernel
def cuts71663 : List PrefixCut := [⟨64,171095325,171095426⟩]
theorem checked71663 : checkPrefixCuts (2^48) 9396944897 10 Manual.Count131072.C071663.packed 64 cuts71663 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000051
