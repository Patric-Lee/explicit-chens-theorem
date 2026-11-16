import PlattAssemblyKernel
import PlattCertificates.Count131072.C022752
import PlattCertificates.Count131072.C022753
import PlattCertificates.Count131072.C022754
import PlattCertificates.Count131072.C022755
import PlattCertificates.Count131072.C022756
import PlattCertificates.Count131072.C022757
import PlattCertificates.Count131072.C022758
import PlattCertificates.Count131072.C022759
import PlattCertificates.Count131072.C022760
import PlattCertificates.Count131072.C022761
import PlattCertificates.Count131072.C022762
import PlattCertificates.Count131072.C022763
import PlattCertificates.Count131072.C022764
import PlattCertificates.Count131072.C022765
import PlattCertificates.Count131072.C022766
import PlattCertificates.Count131072.C022767
import PlattCertificates.Count131072.C022768
import PlattCertificates.Count131072.C022769
import PlattCertificates.Count131072.C022770
import PlattCertificates.Count131072.C022771
import PlattCertificates.Count131072.C022772
import PlattCertificates.Count131072.C022773
import PlattCertificates.Count131072.C022774
import PlattCertificates.Count131072.C022775
import PlattCertificates.Count131072.C022776
import PlattCertificates.Count131072.C022777
import PlattCertificates.Count131072.C022778
import PlattCertificates.Count131072.C022779
import PlattCertificates.Count131072.C022780
import PlattCertificates.Count131072.C022781
import PlattCertificates.Count131072.C022782
import PlattCertificates.Count131072.C022783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22752 : List PrefixCut := [⟨32,138753296,138753376⟩,
⟨124,545484101,545484420⟩,
⟨128,563110384,563110712⟩]
theorem checked22752 : checkPrefixCuts (2^48) 2986082305 9 Manual.Count131072.C022752.packed 128 cuts22752 = true := by
 decide +kernel
def pointBounds22752 : List (Nat × Nat × Nat) := [(2986115072,101686766927137,101687148259031),(2986209280,101687173657942,101687554990075)]
theorem point_links_checked22752 : (cuts22752.take 2).map (fun c => (2986082305-1+2*2^9*c.k,101686628173841+c.lower,101687009505655+c.upper)) = pointBounds22752 := by
 decide +kernel
def cuts22753 : List PrefixCut := [⟨88,389939978,389940200⟩,
⟨128,568646781,568647098⟩]
theorem checked22753 : checkPrefixCuts (2^48) 2986213377 9 Manual.Count131072.C022753.packed 128 cuts22753 = true := by
 decide +kernel
def pointBounds22753 : List (Nat × Nat × Nat) := [(2986303488,101687581224203,101687962556567)]
theorem point_links_checked22753 : (cuts22753.take 1).map (fun c => (2986213377-1+2*2^9*c.k,101687191284225+c.lower,101687572616367+c.upper)) = pointBounds22753 := by
 decide +kernel
def cuts22754 : List PrefixCut := [⟨52,229317914,229318040⟩,
⟨128,559856486,559856800⟩]
theorem checked22754 : checkPrefixCuts (2^48) 2986344449 9 Manual.Count131072.C022754.packed 128 cuts22754 = true := by
 decide +kernel
def pointBounds22754 : List (Nat × Nat × Nat) := [(2986397696,101687989248920,101688370581505)]
theorem point_links_checked22754 : (cuts22754.take 1).map (fun c => (2986344449-1+2*2^9*c.k,101687759931006+c.lower,101688141263465+c.upper)) = pointBounds22754 := by
 decide +kernel
def cuts22755 : List PrefixCut := [⟨16,72195195,72195234⟩,
⟨108,483775578,483775853⟩,
⟨128,573309319,573309645⟩]
theorem checked22755 : checkPrefixCuts (2^48) 2986475521 9 Manual.Count131072.C022755.packed 128 cuts22755 = true := by
 decide +kernel
def pointBounds22755 : List (Nat × Nat × Nat) := [(2986491904,101688391982687,101688773315499),(2986586112,101688803563070,101689184896118)]
theorem point_links_checked22755 : (cuts22755.take 2).map (fun c => (2986475521-1+2*2^9*c.k,101688319787492+c.lower,101688701120265+c.upper)) = pointBounds22755 := by
 decide +kernel
def cuts22756 : List PrefixCut := [⟨72,315625046,315625225⟩,
⟨128,562257664,562257978⟩]
theorem checked22756 : checkPrefixCuts (2^48) 2986606593 9 Manual.Count131072.C022756.packed 128 cuts22756 = true := by
 decide +kernel
def pointBounds22756 : List (Nat × Nat × Nat) := [(2986680320,101689208721857,101689590055135)]
theorem point_links_checked22756 : (cuts22756.take 1).map (fun c => (2986606593-1+2*2^9*c.k,101688893096811+c.lower,101689274429910+c.upper)) = pointBounds22756 := by
 decide +kernel
def cuts22757 : List PrefixCut := [⟨36,161811800,161811894⟩,
⟨128,571751134,571751460⟩]
theorem checked22757 : checkPrefixCuts (2^48) 2986737665 9 Manual.Count131072.C022757.packed 128 cuts22757 = true := by
 decide +kernel
def pointBounds22757 : List (Nat × Nat × Nat) := [(2986774528,101689617166275,101689998499782),(2986868736,101690027105609,101690408439348)]
theorem point_links_checked22757 : (cuts22757.take 2).map (fun c => (2986737665-1+2*2^9*c.k,101689455354475+c.lower,101689836687888+c.upper)) = pointBounds22757 := by
 decide +kernel
def cuts22758 : List PrefixCut := [⟨92,411057238,411057471⟩,
⟨128,570029808,570030131⟩]
theorem checked22758 : checkPrefixCuts (2^48) 2986868737 9 Manual.Count131072.C022758.packed 128 cuts22758 = true := by
 decide +kernel
def pointBounds22758 : List (Nat × Nat × Nat) := [(2986962944,101690438162847,101690819496819)]
theorem point_links_checked22758 : (cuts22758.take 1).map (fun c => (2986868737-1+2*2^9*c.k,101690027105609+c.lower,101690408439348+c.upper)) = pointBounds22758 := by
 decide +kernel
def cuts22759 : List PrefixCut := [⟨56,256123686,256123835⟩,
⟨128,566612685,566613012⟩]
theorem checked22759 : checkPrefixCuts (2^48) 2986999809 9 Manual.Count131072.C022759.packed 128 cuts22759 = true := by
 decide +kernel
def pointBounds22759 : List (Nat × Nat × Nat) := [(2987057152,101690853259103,101691234593314)]
theorem point_links_checked22759 : (cuts22759.take 1).map (fun c => (2986999809-1+2*2^9*c.k,101690597135417+c.lower,101690978469479+c.upper)) = pointBounds22759 := by
 decide +kernel
def cuts22760 : List PrefixCut := [⟨20,86784782,86784831⟩,
⟨112,496389748,496390032⟩,
⟨128,566681827,566682148⟩]
theorem checked22760 : checkPrefixCuts (2^48) 2987130881 9 Manual.Count131072.C022760.packed 128 cuts22760 = true := by
 decide +kernel
def pointBounds22760 : List (Nat × Nat × Nat) := [(2987151360,101691250532884,101691631867322),(2987245568,101691660137850,101692041472523)]
theorem point_links_checked22760 : (cuts22760.take 2).map (fun c => (2987130881-1+2*2^9*c.k,101691163748102+c.lower,101691545082491+c.upper)) = pointBounds22760 := by
 decide +kernel
def cuts22761 : List PrefixCut := [⟨76,339676855,339677046⟩,
⟨128,572310341,572310669⟩]
theorem checked22761 : checkPrefixCuts (2^48) 2987261953 9 Manual.Count131072.C022761.packed 128 cuts22761 = true := by
 decide +kernel
def pointBounds22761 : List (Nat × Nat × Nat) := [(2987339776,101692070106784,101692451441685)]
theorem point_links_checked22761 : (cuts22761.take 1).map (fun c => (2987261953-1+2*2^9*c.k,101691730429929+c.lower,101692111764639+c.upper)) = pointBounds22761 := by
 decide +kernel
def cuts22762 : List PrefixCut := [⟨40,180337579,180337685⟩,
⟨128,572567969,572568294⟩]
theorem checked22762 : checkPrefixCuts (2^48) 2987393025 9 Manual.Count131072.C022762.packed 128 cuts22762 = true := by
 decide +kernel
def pointBounds22762 : List (Nat × Nat × Nat) := [(2987433984,101692483077849,101692864412993)]
theorem point_links_checked22762 : (cuts22762.take 1).map (fun c => (2987393025-1+2*2^9*c.k,101692302740270+c.lower,101692684075308+c.upper)) = pointBounds22762 := by
 decide +kernel
def cuts22763 : List PrefixCut := [⟨4,19031776,19031787⟩,
⟨96,427454439,427454687⟩,
⟨128,571412143,571412471⟩]
theorem checked22763 : checkPrefixCuts (2^48) 2987524097 9 Manual.Count131072.C022763.packed 128 cuts22763 = true := by
 decide +kernel
def pointBounds22763 : List (Nat × Nat × Nat) := [(2987528192,101692894340015,101693275675389),(2987622400,101693302762678,101693684098289)]
theorem point_links_checked22763 : (cuts22763.take 2).map (fun c => (2987524097-1+2*2^9*c.k,101692875308239+c.lower,101693256643602+c.upper)) = pointBounds22763 := by
 decide +kernel
def cuts22764 : List PrefixCut := [⟨60,259647386,259647539⟩,
⟨128,557632433,557632752⟩]
theorem checked22764 : checkPrefixCuts (2^48) 2987655169 9 Manual.Count131072.C022764.packed 128 cuts22764 = true := by
 decide +kernel
def pointBounds22764 : List (Nat × Nat × Nat) := [(2987716608,101693706367768,101694087703612)]
theorem point_links_checked22764 : (cuts22764.take 1).map (fun c => (2987655169-1+2*2^9*c.k,101693446720382+c.lower,101693828056073+c.upper)) = pointBounds22764 := by
 decide +kernel
def cuts22765 : List PrefixCut := [⟨24,107491474,107491534⟩,
⟨116,518513381,518513679⟩,
⟨128,572492602,572492932⟩]
theorem checked22765 : checkPrefixCuts (2^48) 2987786241 9 Manual.Count131072.C022765.packed 128 cuts22765 = true := by
 decide +kernel
def pointBounds22765 : List (Nat × Nat × Nat) := [(2987810816,101694111844289,101694493180359),(2987905024,101694522866196,101694904202504)]
theorem point_links_checked22765 : (cuts22765.take 2).map (fun c => (2987786241-1+2*2^9*c.k,101694004352815+c.lower,101694385688825+c.upper)) = pointBounds22765 := by
 decide +kernel
def cuts22766 : List PrefixCut := [⟨80,356370286,356370490⟩,
⟨128,568040011,568040338⟩]
theorem checked22766 : checkPrefixCuts (2^48) 2987917313 9 Manual.Count131072.C022766.packed 128 cuts22766 = true := by
 decide +kernel
def pointBounds22766 : List (Nat × Nat × Nat) := [(2987999232,101694933215703,101695314552247)]
theorem point_links_checked22766 : (cuts22766.take 1).map (fun c => (2987917313-1+2*2^9*c.k,101694576845417+c.lower,101694958181757+c.upper)) = pointBounds22766 := by
 decide +kernel
def cuts22767 : List PrefixCut := [⟨44,194804635,194804746⟩,
⟨128,567732425,567732750⟩]
theorem checked22767 : checkPrefixCuts (2^48) 2988048385 9 Manual.Count131072.C022767.packed 128 cuts22767 = true := by
 decide +kernel
def pointBounds22767 : List (Nat × Nat × Nat) := [(2988093440,101695339690063,101695721026841)]
theorem point_links_checked22767 : (cuts22767.take 1).map (fun c => (2988048385-1+2*2^9*c.k,101695144885428+c.lower,101695526222095+c.upper)) = pointBounds22767 := by
 decide +kernel
def cuts22768 : List PrefixCut := [⟨8,36736435,36736455⟩,
⟨100,437156785,437157037⟩,
⟨128,564787545,564787864⟩]
theorem checked22768 : checkPrefixCuts (2^48) 2988179457 9 Manual.Count131072.C022768.packed 128 cuts22768 = true := by
 decide +kernel
def pointBounds22768 : List (Nat × Nat × Nat) := [(2988187648,101695749354288,101696130691300),(2988281856,101696149774638,101696531111882)]
theorem point_links_checked22768 : (cuts22768.take 2).map (fun c => (2988179457-1+2*2^9*c.k,101695712617853+c.lower,101696093954845+c.upper)) = pointBounds22768 := by
 decide +kernel
def cuts22769 : List PrefixCut := [⟨64,281442580,281442741⟩,
⟨128,566646521,566646846⟩]
theorem checked22769 : checkPrefixCuts (2^48) 2988310529 9 Manual.Count131072.C022769.packed 128 cuts22769 = true := by
 decide +kernel
def pointBounds22769 : List (Nat × Nat × Nat) := [(2988376064,101696558847978,101696940185450)]
theorem point_links_checked22769 : (cuts22769.take 1).map (fun c => (2988310529-1+2*2^9*c.k,101696277405398+c.lower,101696658742709+c.upper)) = pointBounds22769 := by
 decide +kernel
def cuts22770 : List PrefixCut := [⟨28,123668054,123668121⟩,
⟨120,530831793,530832088⟩,
⟨128,563325220,563325534⟩]
theorem checked22770 : checkPrefixCuts (2^48) 2988441601 9 Manual.Count131072.C022770.packed 128 cuts22770 = true := by
 decide +kernel
def pointBounds22770 : List (Nat × Nat × Nat) := [(2988470272,101696967719973,101697349057676),(2988564480,101697374883712,101697756221643)]
theorem point_links_checked22770 : (cuts22770.take 2).map (fun c => (2988441601-1+2*2^9*c.k,101696844051919+c.lower,101697225389555+c.upper)) = pointBounds22770 := by
 decide +kernel
def cuts22771 : List PrefixCut := [⟨84,373338890,373339100⟩,
⟨128,568009576,568009897⟩]
theorem checked22771 : checkPrefixCuts (2^48) 2988572673 9 Manual.Count131072.C022771.packed 128 cuts22771 = true := by
 decide +kernel
def pointBounds22771 : List (Nat × Nat × Nat) := [(2988658688,101697780716029,101698162054189)]
theorem point_links_checked22771 : (cuts22771.take 1).map (fun c => (2988572673-1+2*2^9*c.k,101697407377139+c.lower,101697788715089+c.upper)) = pointBounds22771 := by
 decide +kernel
def cuts22772 : List PrefixCut := [⟨48,211525604,211525728⟩,
⟨128,565724371,565724696⟩]
theorem checked22772 : checkPrefixCuts (2^48) 2988703745 9 Manual.Count131072.C022772.packed 128 cuts22772 = true := by
 decide +kernel
def pointBounds22772 : List (Nat × Nat × Nat) := [(2988752896,101698186912319,101698568250714)]
theorem point_links_checked22772 : (cuts22772.take 1).map (fun c => (2988703745-1+2*2^9*c.k,101697975386715+c.lower,101698356724986+c.upper)) = pointBounds22772 := by
 decide +kernel
def cuts22773 : List PrefixCut := [⟨12,51608047,51608079⟩,
⟨104,451657394,451657663⟩,
⟨128,554587078,554587407⟩]
theorem checked22773 : checkPrefixCuts (2^48) 2988834817 9 Manual.Count131072.C022773.packed 128 cuts22773 = true := by
 decide +kernel
def pointBounds22773 : List (Nat × Nat × Nat) := [(2988847104,101698592719133,101698974057761),(2988941312,101698992768480,101699374107345)]
theorem point_links_checked22773 : (cuts22773.take 2).map (fun c => (2988834817-1+2*2^9*c.k,101698541111086+c.lower,101698922449682+c.upper)) = pointBounds22773 := by
 decide +kernel
def cuts22774 : List PrefixCut := [⟨68,300497204,300497370⟩,
⟨128,566993141,566993461⟩]
theorem checked22774 : checkPrefixCuts (2^48) 2988965889 9 Manual.Count131072.C022774.packed 128 cuts22774 = true := by
 decide +kernel
def pointBounds22774 : List (Nat × Nat × Nat) := [(2989035520,101699396195368,101699777534459)]
theorem point_links_checked22774 : (cuts22774.take 1).map (fun c => (2988965889-1+2*2^9*c.k,101699095698164+c.lower,101699477037089+c.upper)) = pointBounds22774 := by
 decide +kernel
def cuts22775 : List PrefixCut := [⟨32,141532512,141532594⟩,
⟨124,546063977,546064289⟩,
⟨128,563389995,563390317⟩]
theorem checked22775 : checkPrefixCuts (2^48) 2989096961 9 Manual.Count131072.C022775.packed 128 cuts22775 = true := by
 decide +kernel
def pointBounds22775 : List (Nat × Nat × Nat) := [(2989129728,101699804223817,101700185563144),(2989223936,101700208755282,101700590094839)]
theorem point_links_checked22775 : (cuts22775.take 2).map (fun c => (2989096961-1+2*2^9*c.k,101699662691305+c.lower,101700044030550+c.upper)) = pointBounds22775 := by
 decide +kernel
def cuts22776 : List PrefixCut := [⟨88,387381057,387381283⟩,
⟨128,566095966,566096291⟩]
theorem checked22776 : checkPrefixCuts (2^48) 2989228033 9 Manual.Count131072.C022776.packed 128 cuts22776 = true := by
 decide +kernel
def pointBounds22776 : List (Nat × Nat × Nat) := [(2989318144,101700613462357,101700994802150)]
theorem point_links_checked22776 : (cuts22776.take 1).map (fun c => (2989228033-1+2*2^9*c.k,101700226081300+c.lower,101700607420867+c.upper)) = pointBounds22776 := by
 decide +kernel
def cuts22777 : List PrefixCut := [⟨52,228804236,228804368⟩,
⟨128,559291975,559292290⟩]
theorem checked22777 : checkPrefixCuts (2^48) 2989359105 9 Manual.Count131072.C022777.packed 128 cuts22777 = true := by
 decide +kernel
def pointBounds22777 : List (Nat × Nat × Nat) := [(2989412352,101701020981502,101701402321526)]
theorem point_links_checked22777 : (cuts22777.take 1).map (fun c => (2989359105-1+2*2^9*c.k,101700792177266+c.lower,101701173517158+c.upper)) = pointBounds22777 := by
 decide +kernel
def cuts22778 : List PrefixCut := [⟨16,69580220,69580262⟩,
⟨108,478109296,478109559⟩,
⟨128,563033506,563033820⟩]
theorem checked22778 : checkPrefixCuts (2^48) 2989490177 9 Manual.Count131072.C022778.packed 128 cuts22778 = true := by
 decide +kernel
def pointBounds22778 : List (Nat × Nat × Nat) := [(2989506560,101701421049461,101701802389710),(2989600768,101701829578537,101702210919007)]
theorem point_links_checked22778 : (cuts22778.take 2).map (fun c => (2989490177-1+2*2^9*c.k,101701351469241+c.lower,101701732809448+c.upper)) = pointBounds22778 := by
 decide +kernel
def cuts22779 : List PrefixCut := [⟨72,316154103,316154276⟩,
⟨128,563667759,563668075⟩]
theorem checked22779 : checkPrefixCuts (2^48) 2989621249 9 Manual.Count131072.C022779.packed 128 cuts22779 = true := by
 decide +kernel
def pointBounds22779 : List (Nat × Nat × Nat) := [(2989694976,101702230656850,101702611997544)]
theorem point_links_checked22779 : (cuts22779.take 1).map (fun c => (2989621249-1+2*2^9*c.k,101701914502747+c.lower,101702295843268+c.upper)) = pointBounds22779 := by
 decide +kernel
def cuts22780 : List PrefixCut := [⟨36,158353531,158353619⟩,
⟨128,566749906,566750226⟩]
theorem checked22780 : checkPrefixCuts (2^48) 2989752321 9 Manual.Count131072.C022780.packed 128 cuts22780 = true := by
 decide +kernel
def pointBounds22780 : List (Nat × Nat × Nat) := [(2989789184,101702636524037,101703017864962),(2989883392,101703044920412,101703426261569)]
theorem point_links_checked22780 : (cuts22780.take 2).map (fun c => (2989752321-1+2*2^9*c.k,101702478170506+c.lower,101702859511343+c.upper)) = pointBounds22780 := by
 decide +kernel
def cuts22781 : List PrefixCut := [⟨92,408477513,408477741⟩,
⟨128,568890159,568890477⟩]
theorem checked22781 : checkPrefixCuts (2^48) 2989883393 9 Manual.Count131072.C022781.packed 128 cuts22781 = true := by
 decide +kernel
def pointBounds22781 : List (Nat × Nat × Nat) := [(2989977600,101703453397925,101703834739310)]
theorem point_links_checked22781 : (cuts22781.take 1).map (fun c => (2989883393-1+2*2^9*c.k,101703044920412+c.lower,101703426261569+c.upper)) = pointBounds22781 := by
 decide +kernel
def cuts22782 : List PrefixCut := [⟨56,252099977,252100123⟩,
⟨128,569053707,569054028⟩]
theorem checked22782 : checkPrefixCuts (2^48) 2990014465 9 Manual.Count131072.C022782.packed 128 cuts22782 = true := by
 decide +kernel
def pointBounds22782 : List (Nat × Nat × Nat) := [(2990071808,101703865910548,101704247252169)]
theorem point_links_checked22782 : (cuts22782.take 1).map (fun c => (2990014465-1+2*2^9*c.k,101703613810571+c.lower,101703995152046+c.upper)) = pointBounds22782 := by
 decide +kernel
def cuts22783 : List PrefixCut := [⟨20,88297557,88297607⟩,
⟨112,492500510,492500794⟩,
⟨128,565357368,565357694⟩]
theorem checked22783 : checkPrefixCuts (2^48) 2990145537 9 Manual.Count131072.C022783.packed 128 cuts22783 = true := by
 decide +kernel
def pointBounds22783 : List (Nat × Nat × Nat) := [(2990166016,101704271161835,101704652503681),(2990260224,101704675364788,101705056706868)]
theorem point_links_checked22783 : (cuts22783.take 2).map (fun c => (2990145537-1+2*2^9*c.k,101704182864278+c.lower,101704564206074+c.upper)) = pointBounds22783 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000086
