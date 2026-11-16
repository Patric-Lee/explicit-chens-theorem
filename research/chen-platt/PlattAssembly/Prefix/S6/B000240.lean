import PlattAssemblyKernel
import PlattCertificates.Count131072.C057680
import PlattCertificates.Count131072.C057681
import PlattCertificates.Count131072.C057682
import PlattCertificates.Count131072.C057683
import PlattCertificates.Count131072.C057684
import PlattCertificates.Count131072.C057685
import PlattCertificates.Count131072.C057686
import PlattCertificates.Count131072.C057687
import PlattCertificates.Count131072.C057688
import PlattCertificates.Count131072.C057689
import PlattCertificates.Count131072.C057690
import PlattCertificates.Count131072.C057691
import PlattCertificates.Count131072.C057692
import PlattCertificates.Count131072.C057693
import PlattCertificates.Count131072.C057694
import PlattCertificates.Count131072.C057695
import PlattCertificates.Count131072.C057696
import PlattCertificates.Count131072.C057697
import PlattCertificates.Count131072.C057698
import PlattCertificates.Count131072.C057699
import PlattCertificates.Count131072.C057700
import PlattCertificates.Count131072.C057701
import PlattCertificates.Count131072.C057702
import PlattCertificates.Count131072.C057703
import PlattCertificates.Count131072.C057704
import PlattCertificates.Count131072.C057705
import PlattCertificates.Count131072.C057706
import PlattCertificates.Count131072.C057707
import PlattCertificates.Count131072.C057708
import PlattCertificates.Count131072.C057709
import PlattCertificates.Count131072.C057710
import PlattCertificates.Count131072.C057711
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000240
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57680 : List PrefixCut := [⟨64,213146335,213146451⟩]
theorem checked57680 : checkPrefixCuts (2^48) 7564165121 10 Manual.Count131072.C057680.packed 64 cuts57680 = true := by
 decide +kernel
def cuts57681 : List PrefixCut := [⟨8,27424464,27424480⟩,
⟨64,215710187,215710312⟩]
theorem checked57681 : checkPrefixCuts (2^48) 7564296193 10 Manual.Count131072.C057681.packed 64 cuts57681 = true := by
 decide +kernel
def pointBounds57681 : List (Nat × Nat × Nat) := [(7564312576,113429778985987,113430167115365)]
theorem point_links_checked57681 : (cuts57681.take 1).map (fun c => (7564296193-1+2*2^10*c.k,113429751561523+c.lower,113430139690885+c.upper)) = pointBounds57681 := by
 decide +kernel
def cuts57682 : List PrefixCut := [⟨60,199743464,199743581⟩,
⟨64,213027331,213027456⟩]
theorem checked57682 : checkPrefixCuts (2^48) 7564427265 10 Manual.Count131072.C057682.packed 64 cuts57682 = true := by
 decide +kernel
def pointBounds57682 : List (Nat × Nat × Nat) := [(7564550144,113430167015174,113430555144778)]
theorem point_links_checked57682 : (cuts57682.take 1).map (fun c => (7564427265-1+2*2^10*c.k,113429967271710+c.lower,113430355401197+c.upper)) = pointBounds57682 := by
 decide +kernel
def cuts57683 : List PrefixCut := [⟨64,215628299,215628420⟩]
theorem checked57683 : checkPrefixCuts (2^48) 7564558337 10 Manual.Count131072.C057683.packed 64 cuts57683 = true := by
 decide +kernel
def cuts57684 : List PrefixCut := [⟨48,162081556,162081650⟩,
⟨64,215066437,215066561⟩]
theorem checked57684 : checkPrefixCuts (2^48) 7564689409 10 Manual.Count131072.C057684.packed 64 cuts57684 = true := by
 decide +kernel
def pointBounds57684 : List (Nat × Nat × Nat) := [(7564787712,113430558008896,113430946138723)]
theorem point_links_checked57684 : (cuts57684.take 1).map (fun c => (7564689409-1+2*2^10*c.k,113430395927340+c.lower,113430784057073+c.upper)) = pointBounds57684 := by
 decide +kernel
def cuts57685 : List PrefixCut := [⟨64,214430160,214430282⟩]
theorem checked57685 : checkPrefixCuts (2^48) 7564820481 10 Manual.Count131072.C057685.packed 64 cuts57685 = true := by
 decide +kernel
def cuts57686 : List PrefixCut := [⟨36,120068851,120068921⟩,
⟨64,211933568,211933690⟩]
theorem checked57686 : checkPrefixCuts (2^48) 7564951553 10 Manual.Count131072.C057686.packed 64 cuts57686 = true := by
 decide +kernel
def pointBounds57686 : List (Nat × Nat × Nat) := [(7565025280,113430945492788,113431333622837)]
theorem point_links_checked57686 : (cuts57686.take 1).map (fun c => (7564951553-1+2*2^10*c.k,113430825423937+c.lower,113431213553916+c.upper)) = pointBounds57686 := by
 decide +kernel
def cuts57687 : List PrefixCut := [⟨64,216803977,216804101⟩]
theorem checked57687 : checkPrefixCuts (2^48) 7565082625 10 Manual.Count131072.C057687.packed 64 cuts57687 = true := by
 decide +kernel
def cuts57688 : List PrefixCut := [⟨24,81221455,81221499⟩,
⟨64,216576980,216577101⟩]
theorem checked57688 : checkPrefixCuts (2^48) 7565213697 10 Manual.Count131072.C057688.packed 64 cuts57688 = true := by
 decide +kernel
def pointBounds57688 : List (Nat × Nat × Nat) := [(7565262848,113431335382937,113431723513206)]
theorem point_links_checked57688 : (cuts57688.take 1).map (fun c => (7565213697-1+2*2^10*c.k,113431254161482+c.lower,113431642291707+c.upper)) = pointBounds57688 := by
 decide +kernel
def cuts57689 : List PrefixCut := [⟨64,213857234,213857354⟩]
theorem checked57689 : checkPrefixCuts (2^48) 7565344769 10 Manual.Count131072.C057689.packed 64 cuts57689 = true := by
 decide +kernel
def cuts57690 : List PrefixCut := [⟨12,42004583,42004605⟩,
⟨64,220289982,220290104⟩]
theorem checked57690 : checkPrefixCuts (2^48) 7565475841 10 Manual.Count131072.C057690.packed 64 cuts57690 = true := by
 decide +kernel
def pointBounds57690 : List (Nat × Nat × Nat) := [(7565500416,113431726600279,113432114730767)]
theorem point_links_checked57690 : (cuts57690.take 1).map (fun c => (7565475841-1+2*2^10*c.k,113431684595696+c.lower,113432072726162+c.upper)) = pointBounds57690 := by
 decide +kernel
def cuts57691 : List PrefixCut := [⟨64,215635628,215635750⟩]
theorem checked57691 : checkPrefixCuts (2^48) 7565606913 10 Manual.Count131072.C057691.packed 64 cuts57691 = true := by
 decide +kernel
def pointBounds57691 : List (Nat × Nat × Nat) := [(7565737984,113432120521306,113432508652016)]
theorem point_links_checked57691 : (cuts57691.take 1).map (fun c => (7565606913-1+2*2^10*c.k,113431904885678+c.lower,113432293016266+c.upper)) = pointBounds57691 := by
 decide +kernel
def cuts57692 : List PrefixCut := [⟨64,213436882,213437002⟩]
theorem checked57692 : checkPrefixCuts (2^48) 7565737985 10 Manual.Count131072.C057692.packed 64 cuts57692 = true := by
 decide +kernel
def cuts57693 : List PrefixCut := [⟨52,173886756,173886850⟩,
⟨64,213805213,213805331⟩]
theorem checked57693 : checkPrefixCuts (2^48) 7565869057 10 Manual.Count131072.C057693.packed 64 cuts57693 = true := by
 decide +kernel
def pointBounds57693 : List (Nat × Nat × Nat) := [(7565975552,113432507844944,113432895975868)]
theorem point_links_checked57693 : (cuts57693.take 1).map (fun c => (7565869057-1+2*2^10*c.k,113432333958188+c.lower,113432722089018+c.upper)) = pointBounds57693 := by
 decide +kernel
def cuts57694 : List PrefixCut := [⟨64,216517262,216517385⟩]
theorem checked57694 : checkPrefixCuts (2^48) 7566000129 10 Manual.Count131072.C057694.packed 64 cuts57694 = true := by
 decide +kernel
def cuts57695 : List PrefixCut := [⟨40,134261143,134261219⟩,
⟨64,215397471,215397594⟩]
theorem checked57695 : checkPrefixCuts (2^48) 7566131201 10 Manual.Count131072.C057695.packed 64 cuts57695 = true := by
 decide +kernel
def pointBounds57695 : List (Nat × Nat × Nat) := [(7566213120,113432898541806,113433286672953)]
theorem point_links_checked57695 : (cuts57695.take 1).map (fun c => (7566131201-1+2*2^10*c.k,113432764280663+c.lower,113433152411734+c.upper)) = pointBounds57695 := by
 decide +kernel
def cuts57696 : List PrefixCut := [⟨64,215654144,215654262⟩]
theorem checked57696 : checkPrefixCuts (2^48) 7566262273 10 Manual.Count131072.C057696.packed 64 cuts57696 = true := by
 decide +kernel
def cuts57697 : List PrefixCut := [⟨28,92480512,92480565⟩,
⟨64,213492785,213492908⟩]
theorem checked57697 : checkPrefixCuts (2^48) 7566393345 10 Manual.Count131072.C057697.packed 64 cuts57697 = true := by
 decide +kernel
def pointBounds57697 : List (Nat × Nat × Nat) := [(7566450688,113433287812790,113433675944155)]
theorem point_links_checked57697 : (cuts57697.take 1).map (fun c => (7566393345-1+2*2^10*c.k,113433195332278+c.lower,113433583463590+c.upper)) = pointBounds57697 := by
 decide +kernel
def cuts57698 : List PrefixCut := [⟨64,214977078,214977199⟩]
theorem checked57698 : checkPrefixCuts (2^48) 7566524417 10 Manual.Count131072.C057698.packed 64 cuts57698 = true := by
 decide +kernel
def cuts57699 : List PrefixCut := [⟨16,53938985,53939014⟩,
⟨64,214303786,214303904⟩]
theorem checked57699 : checkPrefixCuts (2^48) 7566655489 10 Manual.Count131072.C057699.packed 64 cuts57699 = true := by
 decide +kernel
def pointBounds57699 : List (Nat × Nat × Nat) := [(7566688256,113433677741126,113434065872711)]
theorem point_links_checked57699 : (cuts57699.take 1).map (fun c => (7566655489-1+2*2^10*c.k,113433623802141+c.lower,113434011933697+c.upper)) = pointBounds57699 := by
 decide +kernel
def cuts57700 : List PrefixCut := [⟨64,215006845,215006966⟩]
theorem checked57700 : checkPrefixCuts (2^48) 7566786561 10 Manual.Count131072.C057700.packed 64 cuts57700 = true := by
 decide +kernel
def cuts57701 : List PrefixCut := [⟨4,12647344,12647352⟩,
⟨64,212845630,212845750⟩]
theorem checked57701 : checkPrefixCuts (2^48) 7566917633 10 Manual.Count131072.C057701.packed 64 cuts57701 = true := by
 decide +kernel
def pointBounds57701 : List (Nat × Nat × Nat) := [(7566925824,113434065760116,113434453891919)]
theorem point_links_checked57701 : (cuts57701.take 1).map (fun c => (7566917633-1+2*2^10*c.k,113434053112772+c.lower,113434441244567+c.upper)) = pointBounds57701 := by
 decide +kernel
def cuts57702 : List PrefixCut := [⟨56,187845698,187845808⟩,
⟨64,213697505,213697630⟩]
theorem checked57702 : checkPrefixCuts (2^48) 7567048705 10 Manual.Count131072.C057702.packed 64 cuts57702 = true := by
 decide +kernel
def pointBounds57702 : List (Nat × Nat × Nat) := [(7567163392,113434453804100,113434841936125)]
theorem point_links_checked57702 : (cuts57702.take 1).map (fun c => (7567048705-1+2*2^10*c.k,113434265958402+c.lower,113434654090317+c.upper)) = pointBounds57702 := by
 decide +kernel
def cuts57703 : List PrefixCut := [⟨64,215739581,215739705⟩]
theorem checked57703 : checkPrefixCuts (2^48) 7567179777 10 Manual.Count131072.C057703.packed 64 cuts57703 = true := by
 decide +kernel
def cuts57704 : List PrefixCut := [⟨44,147630672,147630754⟩,
⟨64,213690084,213690203⟩]
theorem checked57704 : checkPrefixCuts (2^48) 7567310849 10 Manual.Count131072.C057704.packed 64 cuts57704 = true := by
 decide +kernel
def pointBounds57704 : List (Nat × Nat × Nat) := [(7567400960,113434843026160,113435231158406)]
theorem point_links_checked57704 : (cuts57704.take 1).map (fun c => (7567310849-1+2*2^10*c.k,113434695395488+c.lower,113435083527652+c.upper)) = pointBounds57704 := by
 decide +kernel
def cuts57705 : List PrefixCut := [⟨64,214467480,214467604⟩]
theorem checked57705 : checkPrefixCuts (2^48) 7567441921 10 Manual.Count131072.C057705.packed 64 cuts57705 = true := by
 decide +kernel
def cuts57706 : List PrefixCut := [⟨32,108980503,108980563⟩,
⟨64,215207675,215207795⟩]
theorem checked57706 : checkPrefixCuts (2^48) 7567572993 10 Manual.Count131072.C057706.packed 64 cuts57706 = true := by
 decide +kernel
def pointBounds57706 : List (Nat × Nat × Nat) := [(7567638528,113435232533555,113435620666022)]
theorem point_links_checked57706 : (cuts57706.take 1).map (fun c => (7567572993-1+2*2^10*c.k,113435123553052+c.lower,113435511685459+c.upper)) = pointBounds57706 := by
 decide +kernel
def cuts57707 : List PrefixCut := [⟨64,216431330,216431456⟩]
theorem checked57707 : checkPrefixCuts (2^48) 7567704065 10 Manual.Count131072.C057707.packed 64 cuts57707 = true := by
 decide +kernel
def cuts57708 : List PrefixCut := [⟨20,66576332,66576372⟩,
⟨64,212410702,212410824⟩]
theorem checked57708 : checkPrefixCuts (2^48) 7567835137 10 Manual.Count131072.C057708.packed 64 cuts57708 = true := by
 decide +kernel
def pointBounds57708 : List (Nat × Nat × Nat) := [(7567876096,113435621768389,113436009901082)]
theorem point_links_checked57708 : (cuts57708.take 1).map (fun c => (7567835137-1+2*2^10*c.k,113435555192057+c.lower,113435943324710+c.upper)) = pointBounds57708 := by
 decide +kernel
def cuts57709 : List PrefixCut := [⟨64,214303848,214303964⟩]
theorem checked57709 : checkPrefixCuts (2^48) 7567966209 10 Manual.Count131072.C057709.packed 64 cuts57709 = true := by
 decide +kernel
def cuts57710 : List PrefixCut := [⟨8,26666845,26666860⟩,
⟨64,212700891,212701011⟩]
theorem checked57710 : checkPrefixCuts (2^48) 7568097281 10 Manual.Count131072.C057710.packed 64 cuts57710 = true := by
 decide +kernel
def pointBounds57710 : List (Nat × Nat × Nat) := [(7568113664,113436008573452,113436396706358)]
theorem point_links_checked57710 : (cuts57710.take 1).map (fun c => (7568097281-1+2*2^10*c.k,113435981906607+c.lower,113436370039498+c.upper)) = pointBounds57710 := by
 decide +kernel
def cuts57711 : List PrefixCut := [⟨60,199419999,199420114⟩,
⟨64,213069105,213069228⟩]
theorem checked57711 : checkPrefixCuts (2^48) 7568228353 10 Manual.Count131072.C057711.packed 64 cuts57711 = true := by
 decide +kernel
def pointBounds57711 : List (Nat × Nat × Nat) := [(7568351232,113436394027497,113436782160623)]
theorem point_links_checked57711 : (cuts57711.take 1).map (fun c => (7568228353-1+2*2^10*c.k,113436194607498+c.lower,113436582740509+c.upper)) = pointBounds57711 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000240
