import PlattAssemblyKernel
import PlattCertificates.Count131072.C066688
import PlattCertificates.Count131072.C066689
import PlattCertificates.Count131072.C066690
import PlattCertificates.Count131072.C066691
import PlattCertificates.Count131072.C066692
import PlattCertificates.Count131072.C066693
import PlattCertificates.Count131072.C066694
import PlattCertificates.Count131072.C066695
import PlattCertificates.Count131072.C066696
import PlattCertificates.Count131072.C066697
import PlattCertificates.Count131072.C066698
import PlattCertificates.Count131072.C066699
import PlattCertificates.Count131072.C066700
import PlattCertificates.Count131072.C066701
import PlattCertificates.Count131072.C066702
import PlattCertificates.Count131072.C066703
import PlattCertificates.Count131072.C066704
import PlattCertificates.Count131072.C066705
import PlattCertificates.Count131072.C066706
import PlattCertificates.Count131072.C066707
import PlattCertificates.Count131072.C066708
import PlattCertificates.Count131072.C066709
import PlattCertificates.Count131072.C066710
import PlattCertificates.Count131072.C066711
import PlattCertificates.Count131072.C066712
import PlattCertificates.Count131072.C066713
import PlattCertificates.Count131072.C066714
import PlattCertificates.Count131072.C066715
import PlattCertificates.Count131072.C066716
import PlattCertificates.Count131072.C066717
import PlattCertificates.Count131072.C066718
import PlattCertificates.Count131072.C066719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000209
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66688 : List PrefixCut := [⟨64,184014337,184014446⟩]
theorem checked66688 : checkPrefixCuts (2^48) 8744861697 10 Manual.Count131072.C066688.packed 64 cuts66688 = true := by
 decide +kernel
def cuts66689 : List PrefixCut := [⟨32,92505028,92505081⟩,
⟨64,185073741,185073849⟩]
theorem checked66689 : checkPrefixCuts (2^48) 8744992769 10 Manual.Count131072.C066689.packed 64 cuts66689 = true := by
 decide +kernel
def pointBounds66689 : List (Nat × Nat × Nat) := [(8745058304,115218958040599,115219347197685)]
theorem point_links_checked66689 : (cuts66689.take 1).map (fun c => (8744992769-1+2*2^10*c.k,115218865535571+c.lower,115219254692604+c.upper)) = pointBounds66689 := by
 decide +kernel
def cuts66690 : List PrefixCut := [⟨64,183043219,183043326⟩]
theorem checked66690 : checkPrefixCuts (2^48) 8745123841 10 Manual.Count131072.C066690.packed 64 cuts66690 = true := by
 decide +kernel
def cuts66691 : List PrefixCut := [⟨38,110526281,110526340⟩,
⟨64,186452184,186452283⟩]
theorem checked66691 : checkPrefixCuts (2^48) 8745254913 10 Manual.Count131072.C066691.packed 64 cuts66691 = true := by
 decide +kernel
def pointBounds66691 : List (Nat × Nat × Nat) := [(8745332736,115219344178812,115219733336119)]
theorem point_links_checked66691 : (cuts66691.take 1).map (fun c => (8745254913-1+2*2^10*c.k,115219233652531+c.lower,115219622809779+c.upper)) = pointBounds66691 := by
 decide +kernel
def cuts66692 : List PrefixCut := [⟨64,183938925,183939029⟩]
theorem checked66692 : checkPrefixCuts (2^48) 8745385985 10 Manual.Count131072.C066692.packed 64 cuts66692 = true := by
 decide +kernel
def cuts66693 : List PrefixCut := [⟨44,125456674,125456752⟩,
⟨64,183582137,183582246⟩]
theorem checked66693 : checkPrefixCuts (2^48) 8745517057 10 Manual.Count131072.C066693.packed 64 cuts66693 = true := by
 decide +kernel
def pointBounds66693 : List (Nat × Nat × Nat) := [(8745607168,115219729500314,115220118657843)]
theorem point_links_checked66693 : (cuts66693.take 1).map (fun c => (8745517057-1+2*2^10*c.k,115219604043640+c.lower,115219993201091+c.upper)) = pointBounds66693 := by
 decide +kernel
def cuts66694 : List PrefixCut := [⟨64,183515025,183515124⟩]
theorem checked66694 : checkPrefixCuts (2^48) 8745648129 10 Manual.Count131072.C066694.packed 64 cuts66694 = true := by
 decide +kernel
def cuts66695 : List PrefixCut := [⟨50,142349367,142349449⟩,
⟨64,182578937,182579040⟩]
theorem checked66695 : checkPrefixCuts (2^48) 8745779201 10 Manual.Count131072.C066695.packed 64 cuts66695 = true := by
 decide +kernel
def pointBounds66695 : List (Nat × Nat × Nat) := [(8745881600,115220113490169,115220502647910)]
theorem point_links_checked66695 : (cuts66695.take 1).map (fun c => (8745779201-1+2*2^10*c.k,115219971140802+c.lower,115220360298461+c.upper)) = pointBounds66695 := by
 decide +kernel
def cuts66696 : List PrefixCut := [⟨64,184056652,184056756⟩]
theorem checked66696 : checkPrefixCuts (2^48) 8745910273 10 Manual.Count131072.C066696.packed 64 cuts66696 = true := by
 decide +kernel
def cuts66697 : List PrefixCut := [⟨56,158307732,158307825⟩,
⟨64,181672348,181672456⟩]
theorem checked66697 : checkPrefixCuts (2^48) 8746041345 10 Manual.Count131072.C066697.packed 64 cuts66697 = true := by
 decide +kernel
def pointBounds66697 : List (Nat × Nat × Nat) := [(8746156032,115220496084123,115220885242082)]
theorem point_links_checked66697 : (cuts66697.take 1).map (fun c => (8746041345-1+2*2^10*c.k,115220337776391+c.lower,115220726934257+c.upper)) = pointBounds66697 := by
 decide +kernel
def cuts66698 : List PrefixCut := [⟨64,183021277,183021385⟩]
theorem checked66698 : checkPrefixCuts (2^48) 8746172417 10 Manual.Count131072.C066698.packed 64 cuts66698 = true := by
 decide +kernel
def cuts66699 : List PrefixCut := [⟨62,178480929,178481032⟩,
⟨64,183662179,183662286⟩]
theorem checked66699 : checkPrefixCuts (2^48) 8746303489 10 Manual.Count131072.C066699.packed 64 cuts66699 = true := by
 decide +kernel
def pointBounds66699 : List (Nat × Nat × Nat) := [(8746430464,115220880950945,115221270109130)]
theorem point_links_checked66699 : (cuts66699.take 1).map (fun c => (8746303489-1+2*2^10*c.k,115220702470016+c.lower,115221091628098+c.upper)) = pointBounds66699 := by
 decide +kernel
def cuts66700 : List PrefixCut := [⟨64,184399604,184399714⟩]
theorem checked66700 : checkPrefixCuts (2^48) 8746434561 10 Manual.Count131072.C066700.packed 64 cuts66700 = true := by
 decide +kernel
def cuts66701 : List PrefixCut := [⟨64,183399225,183399326⟩]
theorem checked66701 : checkPrefixCuts (2^48) 8746565633 10 Manual.Count131072.C066701.packed 64 cuts66701 = true := by
 decide +kernel
def cuts66702 : List PrefixCut := [⟨4,11231062,11231069⟩,
⟨64,183975719,183975829⟩]
theorem checked66702 : checkPrefixCuts (2^48) 8746696705 10 Manual.Count131072.C066702.packed 64 cuts66702 = true := by
 decide +kernel
def pointBounds66702 : List (Nat × Nat × Nat) := [(8746704896,115221265162086,115221654320493)]
theorem point_links_checked66702 : (cuts66702.take 1).map (fun c => (8746696705-1+2*2^10*c.k,115221253931024+c.lower,115221643089424+c.upper)) = pointBounds66702 := by
 decide +kernel
def cuts66703 : List PrefixCut := [⟨64,182589231,182589340⟩]
theorem checked66703 : checkPrefixCuts (2^48) 8746827777 10 Manual.Count131072.C066703.packed 64 cuts66703 = true := by
 decide +kernel
def cuts66704 : List PrefixCut := [⟨10,28961735,28961754⟩,
⟨64,183326622,183326732⟩]
theorem checked66704 : checkPrefixCuts (2^48) 8746958849 10 Manual.Count131072.C066704.packed 64 cuts66704 = true := by
 decide +kernel
def pointBounds66704 : List (Nat × Nat × Nat) := [(8746979328,115221649457709,115222038616347)]
theorem point_links_checked66704 : (cuts66704.take 1).map (fun c => (8746958849-1+2*2^10*c.k,115221620495974+c.lower,115222009654593+c.upper)) = pointBounds66704 := by
 decide +kernel
def cuts66705 : List PrefixCut := [⟨64,183967455,183967559⟩]
theorem checked66705 : checkPrefixCuts (2^48) 8747089921 10 Manual.Count131072.C066705.packed 64 cuts66705 = true := by
 decide +kernel
def cuts66706 : List PrefixCut := [⟨16,46079926,46079954⟩,
⟨64,183288957,183289068⟩]
theorem checked66706 : checkPrefixCuts (2^48) 8747220993 10 Manual.Count131072.C066706.packed 64 cuts66706 = true := by
 decide +kernel
def pointBounds66706 : List (Nat × Nat × Nat) := [(8747253760,115222033869977,115222423028838)]
theorem point_links_checked66706 : (cuts66706.take 1).map (fun c => (8747220993-1+2*2^10*c.k,115221987790051+c.lower,115222376948884+c.upper)) = pointBounds66706 := by
 decide +kernel
def cuts66707 : List PrefixCut := [⟨64,184927292,184927399⟩]
theorem checked66707 : checkPrefixCuts (2^48) 8747352065 10 Manual.Count131072.C066707.packed 64 cuts66707 = true := by
 decide +kernel
def cuts66708 : List PrefixCut := [⟨22,63229241,63229274⟩,
⟨64,184280959,184281067⟩]
theorem checked66708 : checkPrefixCuts (2^48) 8747483137 10 Manual.Count131072.C066708.packed 64 cuts66708 = true := by
 decide +kernel
def pointBounds66708 : List (Nat × Nat × Nat) := [(8747528192,115222419235541,115222808394625)]
theorem point_links_checked66708 : (cuts66708.take 1).map (fun c => (8747483137-1+2*2^10*c.k,115222356006300+c.lower,115222745165351+c.upper)) = pointBounds66708 := by
 decide +kernel
def cuts66709 : List PrefixCut := [⟨64,184052969,184053076⟩]
theorem checked66709 : checkPrefixCuts (2^48) 8747614209 10 Manual.Count131072.C066709.packed 64 cuts66709 = true := by
 decide +kernel
def cuts66710 : List PrefixCut := [⟨28,81053219,81053263⟩,
⟨64,185433800,185433907⟩]
theorem checked66710 : checkPrefixCuts (2^48) 8747745281 10 Manual.Count131072.C066710.packed 64 cuts66710 = true := by
 decide +kernel
def pointBounds66710 : List (Nat × Nat × Nat) := [(8747802624,115222805393447,115223194552757)]
theorem point_links_checked66710 : (cuts66710.take 1).map (fun c => (8747745281-1+2*2^10*c.k,115222724340228+c.lower,115223113499494+c.upper)) = pointBounds66710 := by
 decide +kernel
def cuts66711 : List PrefixCut := [⟨64,183049990,183050102⟩]
theorem checked66711 : checkPrefixCuts (2^48) 8747876353 10 Manual.Count131072.C066711.packed 64 cuts66711 = true := by
 decide +kernel
def cuts66712 : List PrefixCut := [⟨34,96527275,96527329⟩,
⟨64,186071738,186071847⟩]
theorem checked66712 : checkPrefixCuts (2^48) 8748007425 10 Manual.Count131072.C066712.packed 64 cuts66712 = true := by
 decide +kernel
def pointBounds66712 : List (Nat × Nat × Nat) := [(8748077056,115223189351293,115223578510832)]
theorem point_links_checked66712 : (cuts66712.take 1).map (fun c => (8748007425-1+2*2^10*c.k,115223092824018+c.lower,115223481983503+c.upper)) = pointBounds66712 := by
 decide +kernel
def cuts66713 : List PrefixCut := [⟨64,183430596,183430704⟩]
theorem checked66713 : checkPrefixCuts (2^48) 8748138497 10 Manual.Count131072.C066713.packed 64 cuts66713 = true := by
 decide +kernel
def cuts66714 : List PrefixCut := [⟨40,113255190,113255263⟩,
⟨64,182173039,182173150⟩]
theorem checked66714 : checkPrefixCuts (2^48) 8748269569 10 Manual.Count131072.C066714.packed 64 cuts66714 = true := by
 decide +kernel
def pointBounds66714 : List (Nat × Nat × Nat) := [(8748351488,115223575581542,115223964741317)]
theorem point_links_checked66714 : (cuts66714.take 1).map (fun c => (8748269569-1+2*2^10*c.k,115223462326352+c.lower,115223851486054+c.upper)) = pointBounds66714 := by
 decide +kernel
def cuts66715 : List PrefixCut := [⟨64,183006842,183006947⟩]
theorem checked66715 : checkPrefixCuts (2^48) 8748400641 10 Manual.Count131072.C066715.packed 64 cuts66715 = true := by
 decide +kernel
def cuts66716 : List PrefixCut := [⟨46,131944690,131944766⟩,
⟨64,183100626,183100730⟩]
theorem checked66716 : checkPrefixCuts (2^48) 8748531713 10 Manual.Count131072.C066716.packed 64 cuts66716 = true := by
 decide +kernel
def pointBounds66716 : List (Nat × Nat × Nat) := [(8748625920,115223959450923,115224348610917)]
theorem point_links_checked66716 : (cuts66716.take 1).map (fun c => (8748531713-1+2*2^10*c.k,115223827506233+c.lower,115224216666151+c.upper)) = pointBounds66716 := by
 decide +kernel
def cuts66717 : List PrefixCut := [⟨64,184030904,184031017⟩]
theorem checked66717 : checkPrefixCuts (2^48) 8748662785 10 Manual.Count131072.C066717.packed 64 cuts66717 = true := by
 decide +kernel
def cuts66718 : List PrefixCut := [⟨52,150182632,150182716⟩,
⟨64,185057683,185057789⟩]
theorem checked66718 : checkPrefixCuts (2^48) 8748793857 10 Manual.Count131072.C066718.packed 64 cuts66718 = true := by
 decide +kernel
def pointBounds66718 : List (Nat × Nat × Nat) := [(8748900352,115224344820395,115224733980614)]
theorem point_links_checked66718 : (cuts66718.take 1).map (fun c => (8748793857-1+2*2^10*c.k,115224194637763+c.lower,115224583797898+c.upper)) = pointBounds66718 := by
 decide +kernel
def cuts66719 : List PrefixCut := [⟨64,182674162,182674268⟩]
theorem checked66719 : checkPrefixCuts (2^48) 8748924929 10 Manual.Count131072.C066719.packed 64 cuts66719 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000209
