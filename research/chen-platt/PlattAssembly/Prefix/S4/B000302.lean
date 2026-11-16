import PlattAssemblyKernel
import PlattCertificates.Count131072.C039664
import PlattCertificates.Count131072.C039665
import PlattCertificates.Count131072.C039666
import PlattCertificates.Count131072.C039667
import PlattCertificates.Count131072.C039668
import PlattCertificates.Count131072.C039669
import PlattCertificates.Count131072.C039670
import PlattCertificates.Count131072.C039671
import PlattCertificates.Count131072.C039672
import PlattCertificates.Count131072.C039673
import PlattCertificates.Count131072.C039674
import PlattCertificates.Count131072.C039675
import PlattCertificates.Count131072.C039676
import PlattCertificates.Count131072.C039677
import PlattCertificates.Count131072.C039678
import PlattCertificates.Count131072.C039679
import PlattCertificates.Count131072.C039680
import PlattCertificates.Count131072.C039681
import PlattCertificates.Count131072.C039682
import PlattCertificates.Count131072.C039683
import PlattCertificates.Count131072.C039684
import PlattCertificates.Count131072.C039685
import PlattCertificates.Count131072.C039686
import PlattCertificates.Count131072.C039687
import PlattCertificates.Count131072.C039688
import PlattCertificates.Count131072.C039689
import PlattCertificates.Count131072.C039690
import PlattCertificates.Count131072.C039691
import PlattCertificates.Count131072.C039692
import PlattCertificates.Count131072.C039693
import PlattCertificates.Count131072.C039694
import PlattCertificates.Count131072.C039695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39664 : List PrefixCut := [⟨64,314917655,314917848⟩]
theorem checked39664 : checkPrefixCuts (2^48) 5202771969 10 Manual.Count131072.C039664.packed 64 cuts39664 = true := by
 decide +kernel
def cuts39665 : List PrefixCut := [⟨4,20070931,20070943⟩,
⟨64,323240964,323241149⟩]
theorem checked39665 : checkPrefixCuts (2^48) 5202903041 10 Manual.Count131072.C039665.packed 64 cuts39665 = true := by
 decide +kernel
def pointBounds39665 : List (Nat × Nat × Nat) := [(5202911232,108760534714381,108760920157190)]
theorem point_links_checked39665 : (cuts39665.take 1).map (fun c => (5202903041-1+2*2^10*c.k,108760514643450+c.lower,108760900086247+c.upper)) = pointBounds39665 := by
 decide +kernel
def cuts39666 : List PrefixCut := [⟨20,99269843,99269904⟩,
⟨64,317173874,317174064⟩]
theorem checked39666 : checkPrefixCuts (2^48) 5203034113 10 Manual.Count131072.C039666.packed 64 cuts39666 = true := by
 decide +kernel
def pointBounds39666 : List (Nat × Nat × Nat) := [(5203075072,108760937154257,108761322597300)]
theorem point_links_checked39666 : (cuts39666.take 1).map (fun c => (5203034113-1+2*2^10*c.k,108760837884414+c.lower,108761223327396+c.upper)) = pointBounds39666 := by
 decide +kernel
def cuts39667 : List PrefixCut := [⟨36,182034625,182034735⟩,
⟨64,323549235,323549428⟩]
theorem checked39667 : checkPrefixCuts (2^48) 5203165185 10 Manual.Count131072.C039667.packed 64 cuts39667 = true := by
 decide +kernel
def pointBounds39667 : List (Nat × Nat × Nat) := [(5203238912,108761337092913,108761722536195)]
theorem point_links_checked39667 : (cuts39667.take 1).map (fun c => (5203165185-1+2*2^10*c.k,108761155058288+c.lower,108761540501460+c.upper)) = pointBounds39667 := by
 decide +kernel
def cuts39668 : List PrefixCut := [⟨52,257546009,257546161⟩,
⟨64,316887417,316887604⟩]
theorem checked39668 : checkPrefixCuts (2^48) 5203296257 10 Manual.Count131072.C039668.packed 64 cuts39668 = true := by
 decide +kernel
def pointBounds39668 : List (Nat × Nat × Nat) := [(5203402752,108761736153532,108762121597049)]
theorem point_links_checked39668 : (cuts39668.take 1).map (fun c => (5203296257-1+2*2^10*c.k,108761478607523+c.lower,108761864050888+c.upper)) = pointBounds39668 := by
 decide +kernel
def cuts39669 : List PrefixCut := [⟨64,316446718,316446904⟩]
theorem checked39669 : checkPrefixCuts (2^48) 5203427329 10 Manual.Count131072.C039669.packed 64 cuts39669 = true := by
 decide +kernel
def cuts39670 : List PrefixCut := [⟨4,21366629,21366641⟩,
⟨64,313030935,313031123⟩]
theorem checked39670 : checkPrefixCuts (2^48) 5203558401 10 Manual.Count131072.C039670.packed 64 cuts39670 = true := by
 decide +kernel
def pointBounds39670 : List (Nat × Nat × Nat) := [(5203566592,108762133308287,108762518752037)]
theorem point_links_checked39670 : (cuts39670.take 1).map (fun c => (5203558401-1+2*2^10*c.k,108762111941658+c.lower,108762497385396+c.upper)) = pointBounds39670 := by
 decide +kernel
def cuts39671 : List PrefixCut := [⟨20,100771889,100771948⟩,
⟨64,319351648,319351839⟩]
theorem checked39671 : checkPrefixCuts (2^48) 5203689473 10 Manual.Count131072.C039671.packed 64 cuts39671 = true := by
 decide +kernel
def pointBounds39671 : List (Nat × Nat × Nat) := [(5203730432,108762525744482,108762911188467)]
theorem point_links_checked39671 : (cuts39671.take 1).map (fun c => (5203689473-1+2*2^10*c.k,108762424972593+c.lower,108762810416519+c.upper)) = pointBounds39671 := by
 decide +kernel
def cuts39672 : List PrefixCut := [⟨36,178820432,178820539⟩,
⟨64,318261831,318262019⟩]
theorem checked39672 : checkPrefixCuts (2^48) 5203820545 10 Manual.Count131072.C039672.packed 64 cuts39672 = true := by
 decide +kernel
def pointBounds39672 : List (Nat × Nat × Nat) := [(5203894272,108762923144673,108763308588897)]
theorem point_links_checked39672 : (cuts39672.take 1).map (fun c => (5203820545-1+2*2^10*c.k,108762744324241+c.lower,108763129768358+c.upper)) = pointBounds39672 := by
 decide +kernel
def cuts39673 : List PrefixCut := [⟨52,250428012,250428165⟩,
⟨64,311384565,311384752⟩]
theorem checked39673 : checkPrefixCuts (2^48) 5203951617 10 Manual.Count131072.C039673.packed 64 cuts39673 = true := by
 decide +kernel
def pointBounds39673 : List (Nat × Nat × Nat) := [(5204058112,108763313014084,108763698458542)]
theorem point_links_checked39673 : (cuts39673.take 1).map (fun c => (5203951617-1+2*2^10*c.k,108763062586072+c.lower,108763448030377+c.upper)) = pointBounds39673 := by
 decide +kernel
def cuts39674 : List PrefixCut := [⟨64,316569084,316569278⟩]
theorem checked39674 : checkPrefixCuts (2^48) 5204082689 10 Manual.Count131072.C039674.packed 64 cuts39674 = true := by
 decide +kernel
def cuts39675 : List PrefixCut := [⟨4,19957703,19957715⟩,
⟨64,322294204,322294392⟩]
theorem checked39675 : checkPrefixCuts (2^48) 5204213761 10 Manual.Count131072.C039675.packed 64 cuts39675 = true := by
 decide +kernel
def pointBounds39675 : List (Nat × Nat × Nat) := [(5204221952,108763710497424,108764095942122)]
theorem point_links_checked39675 : (cuts39675.take 1).map (fun c => (5204213761-1+2*2^10*c.k,108763690539721+c.lower,108764075984407+c.upper)) = pointBounds39675 := by
 decide +kernel
def cuts39676 : List PrefixCut := [⟨20,98812171,98812229⟩,
⟨64,316012317,316012504⟩]
theorem checked39676 : checkPrefixCuts (2^48) 5204344833 10 Manual.Count131072.C039676.packed 64 cuts39676 = true := by
 decide +kernel
def pointBounds39676 : List (Nat × Nat × Nat) := [(5204385792,108764111646096,108764497091028)]
theorem point_links_checked39676 : (cuts39676.take 1).map (fun c => (5204344833-1+2*2^10*c.k,108764012833925+c.lower,108764398278799+c.upper)) = pointBounds39676 := by
 decide +kernel
def cuts39677 : List PrefixCut := [⟨36,177229500,177229605⟩,
⟨64,315139036,315139225⟩]
theorem checked39677 : checkPrefixCuts (2^48) 5204475905 10 Manual.Count131072.C039677.packed 64 cuts39677 = true := by
 decide +kernel
def pointBounds39677 : List (Nat × Nat × Nat) := [(5204549632,108764506075742,108764891520908)]
theorem point_links_checked39677 : (cuts39677.take 1).map (fun c => (5204475905-1+2*2^10*c.k,108764328846242+c.lower,108764714291303+c.upper)) = pointBounds39677 := by
 decide +kernel
def cuts39678 : List PrefixCut := [⟨52,258941351,258941505⟩,
⟨64,317240278,317240466⟩]
theorem checked39678 : checkPrefixCuts (2^48) 5204606977 10 Manual.Count131072.C039678.packed 64 cuts39678 = true := by
 decide +kernel
def pointBounds39678 : List (Nat × Nat × Nat) := [(5204713472,108764902926629,108765288372033)]
theorem point_links_checked39678 : (cuts39678.take 1).map (fun c => (5204606977-1+2*2^10*c.k,108764643985278+c.lower,108765029430528+c.upper)) = pointBounds39678 := by
 decide +kernel
def cuts39679 : List PrefixCut := [⟨64,311067142,311067325⟩]
theorem checked39679 : checkPrefixCuts (2^48) 5204738049 10 Manual.Count131072.C039679.packed 64 cuts39679 = true := by
 decide +kernel
def cuts39680 : List PrefixCut := [⟨4,20279665,20279677⟩,
⟨64,318630321,318630511⟩]
theorem checked39680 : checkPrefixCuts (2^48) 5204869121 10 Manual.Count131072.C039680.packed 64 cuts39680 = true := by
 decide +kernel
def pointBounds39680 : List (Nat × Nat × Nat) := [(5204877312,108765292572363,108765678017996)]
theorem point_links_checked39680 : (cuts39680.take 1).map (fun c => (5204869121-1+2*2^10*c.k,108765272292698+c.lower,108765657738319+c.upper)) = pointBounds39680 := by
 decide +kernel
def cuts39681 : List PrefixCut := [⟨20,99827198,99827260⟩,
⟨64,319271242,319271435⟩]
theorem checked39681 : checkPrefixCuts (2^48) 5205000193 10 Manual.Count131072.C039681.packed 64 cuts39681 = true := by
 decide +kernel
def pointBounds39681 : List (Nat × Nat × Nat) := [(5205041152,108765690750217,108766076196090)]
theorem point_links_checked39681 : (cuts39681.take 1).map (fun c => (5205000193-1+2*2^10*c.k,108765590923019+c.lower,108765976368830+c.upper)) = pointBounds39681 := by
 decide +kernel
def cuts39682 : List PrefixCut := [⟨36,177639794,177639898⟩,
⟨64,315423798,315423984⟩]
theorem checked39682 : checkPrefixCuts (2^48) 5205131265 10 Manual.Count131072.C039682.packed 64 cuts39682 = true := by
 decide +kernel
def pointBounds39682 : List (Nat × Nat × Nat) := [(5205204992,108766087834055,108766473280163)]
theorem point_links_checked39682 : (cuts39682.take 1).map (fun c => (5205131265-1+2*2^10*c.k,108765910194261+c.lower,108766295640265+c.upper)) = pointBounds39682 := by
 decide +kernel
def cuts39683 : List PrefixCut := [⟨52,250202754,250202900⟩,
⟨64,309035079,309035260⟩]
theorem checked39683 : checkPrefixCuts (2^48) 5205262337 10 Manual.Count131072.C039683.packed 64 cuts39683 = true := by
 decide +kernel
def pointBounds39683 : List (Nat × Nat × Nat) := [(5205368832,108766475820813,108766861267149)]
theorem point_links_checked39683 : (cuts39683.take 1).map (fun c => (5205262337-1+2*2^10*c.k,108766225618059+c.lower,108766611064249+c.upper)) = pointBounds39683 := by
 decide +kernel
def cuts39684 : List PrefixCut := [⟨64,319625609,319625798⟩]
theorem checked39684 : checkPrefixCuts (2^48) 5205393409 10 Manual.Count131072.C039684.packed 64 cuts39684 = true := by
 decide +kernel
def cuts39685 : List PrefixCut := [⟨4,19682315,19682327⟩,
⟨64,320320483,320320674⟩]
theorem checked39685 : checkPrefixCuts (2^48) 5205524481 10 Manual.Count131072.C039685.packed 64 cuts39685 = true := by
 decide +kernel
def pointBounds39685 : List (Nat × Nat × Nat) := [(5205532672,108766873961062,108767259407634)]
theorem point_links_checked39685 : (cuts39685.take 1).map (fun c => (5205524481-1+2*2^10*c.k,108766854278747+c.lower,108767239725307+c.upper)) = pointBounds39685 := by
 decide +kernel
def cuts39686 : List PrefixCut := [⟨20,96408175,96408233⟩,
⟨64,314310617,314310806⟩]
theorem checked39686 : checkPrefixCuts (2^48) 5205655553 10 Manual.Count131072.C039686.packed 64 cuts39686 = true := by
 decide +kernel
def pointBounds39686 : List (Nat × Nat × Nat) := [(5205696512,108767271007405,108767656454214)]
theorem point_links_checked39686 : (cuts39686.take 1).map (fun c => (5205655553-1+2*2^10*c.k,108767174599230+c.lower,108767560045981+c.upper)) = pointBounds39686 := by
 decide +kernel
def cuts39687 : List PrefixCut := [⟨36,178590701,178590809⟩,
⟨64,316573651,316573840⟩]
theorem checked39687 : checkPrefixCuts (2^48) 5205786625 10 Manual.Count131072.C039687.packed 64 cuts39687 = true := by
 decide +kernel
def pointBounds39687 : List (Nat × Nat × Nat) := [(5205860352,108767667500548,108768052947596)]
theorem point_links_checked39687 : (cuts39687.take 1).map (fun c => (5205786625-1+2*2^10*c.k,108767488909847+c.lower,108767874356787+c.upper)) = pointBounds39687 := by
 decide +kernel
def cuts39688 : List PrefixCut := [⟨52,256389063,256389215⟩,
⟨64,315159918,315160103⟩]
theorem checked39688 : checkPrefixCuts (2^48) 5205917697 10 Manual.Count131072.C039688.packed 64 cuts39688 = true := by
 decide +kernel
def pointBounds39688 : List (Nat × Nat × Nat) := [(5206024192,108768061872561,108768447319842)]
theorem point_links_checked39688 : (cuts39688.take 1).map (fun c => (5205917697-1+2*2^10*c.k,108767805483498+c.lower,108768190930627+c.upper)) = pointBounds39688 := by
 decide +kernel
def cuts39689 : List PrefixCut := [⟨64,316773958,316774148⟩]
theorem checked39689 : checkPrefixCuts (2^48) 5206048769 10 Manual.Count131072.C039689.packed 64 cuts39689 = true := by
 decide +kernel
def cuts39690 : List PrefixCut := [⟨4,19517643,19517654⟩,
⟨64,316279375,316279565⟩]
theorem checked39690 : checkPrefixCuts (2^48) 5206179841 10 Manual.Count131072.C039690.packed 64 cuts39690 = true := by
 decide +kernel
def pointBounds39690 : List (Nat × Nat × Nat) := [(5206188032,108768456935017,108768842382532)]
theorem point_links_checked39690 : (cuts39690.take 1).map (fun c => (5206179841-1+2*2^10*c.k,108768437417374+c.lower,108768822864878+c.upper)) = pointBounds39690 := by
 decide +kernel
def cuts39691 : List PrefixCut := [⟨20,97693573,97693632⟩,
⟨64,312432920,312433109⟩]
theorem checked39691 : checkPrefixCuts (2^48) 5206310913 10 Manual.Count131072.C039691.packed 64 cuts39691 = true := by
 decide +kernel
def pointBounds39691 : List (Nat × Nat × Nat) := [(5206351872,108768851390322,108769236838075)]
theorem point_links_checked39691 : (cuts39691.take 1).map (fun c => (5206310913-1+2*2^10*c.k,108768753696749+c.lower,108769139144443+c.upper)) = pointBounds39691 := by
 decide +kernel
def cuts39692 : List PrefixCut := [⟨36,179757574,179757684⟩,
⟨64,319182824,319183018⟩]
theorem checked39692 : checkPrefixCuts (2^48) 5206441985 10 Manual.Count131072.C039692.packed 64 cuts39692 = true := by
 decide +kernel
def pointBounds39692 : List (Nat × Nat × Nat) := [(5206515712,108769245887243,108769631335236)]
theorem point_links_checked39692 : (cuts39692.take 1).map (fun c => (5206441985-1+2*2^10*c.k,108769066129669+c.lower,108769451577552+c.upper)) = pointBounds39692 := by
 decide +kernel
def cuts39693 : List PrefixCut := [⟨52,259546371,259546525⟩,
⟨64,317823287,317823475⟩]
theorem checked39693 : checkPrefixCuts (2^48) 5206573057 10 Manual.Count131072.C039693.packed 64 cuts39693 = true := by
 decide +kernel
def pointBounds39693 : List (Nat × Nat × Nat) := [(5206679552,108769644858864,108770030307095)]
theorem point_links_checked39693 : (cuts39693.take 1).map (fun c => (5206573057-1+2*2^10*c.k,108769385312493+c.lower,108769770760570+c.upper)) = pointBounds39693 := by
 decide +kernel
def cuts39694 : List PrefixCut := [⟨64,319220800,319220994⟩]
theorem checked39694 : checkPrefixCuts (2^48) 5206704129 10 Manual.Count131072.C039694.packed 64 cuts39694 = true := by
 decide +kernel
def cuts39695 : List PrefixCut := [⟨4,19893597,19893609⟩,
⟨64,318564088,318564275⟩]
theorem checked39695 : checkPrefixCuts (2^48) 5206835201 10 Manual.Count131072.C039695.packed 64 cuts39695 = true := by
 decide +kernel
def pointBounds39695 : List (Nat × Nat × Nat) := [(5206843392,108770042250177,108770427698648)]
theorem point_links_checked39695 : (cuts39695.take 1).map (fun c => (5206835201-1+2*2^10*c.k,108770022356580+c.lower,108770407805039+c.upper)) = pointBounds39695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000302
