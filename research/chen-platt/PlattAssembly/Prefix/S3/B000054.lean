import PlattAssemblyKernel
import PlattCertificates.Count131072.C021728
import PlattCertificates.Count131072.C021729
import PlattCertificates.Count131072.C021730
import PlattCertificates.Count131072.C021731
import PlattCertificates.Count131072.C021732
import PlattCertificates.Count131072.C021733
import PlattCertificates.Count131072.C021734
import PlattCertificates.Count131072.C021735
import PlattCertificates.Count131072.C021736
import PlattCertificates.Count131072.C021737
import PlattCertificates.Count131072.C021738
import PlattCertificates.Count131072.C021739
import PlattCertificates.Count131072.C021740
import PlattCertificates.Count131072.C021741
import PlattCertificates.Count131072.C021742
import PlattCertificates.Count131072.C021743
import PlattCertificates.Count131072.C021744
import PlattCertificates.Count131072.C021745
import PlattCertificates.Count131072.C021746
import PlattCertificates.Count131072.C021747
import PlattCertificates.Count131072.C021748
import PlattCertificates.Count131072.C021749
import PlattCertificates.Count131072.C021750
import PlattCertificates.Count131072.C021751
import PlattCertificates.Count131072.C021752
import PlattCertificates.Count131072.C021753
import PlattCertificates.Count131072.C021754
import PlattCertificates.Count131072.C021755
import PlattCertificates.Count131072.C021756
import PlattCertificates.Count131072.C021757
import PlattCertificates.Count131072.C021758
import PlattCertificates.Count131072.C021759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21728 : List PrefixCut := [⟨58,264114540,264114696⟩,
⟨128,588328393,588328739⟩]
theorem checked21728 : checkPrefixCuts (2^48) 2851864577 9 Manual.Count131072.C021728.packed 128 cuts21728 = true := by
 decide +kernel
def pointBounds21728 : List (Nat × Nat × Nat) := [(2851923968,101092939162922,101093320155316)]
theorem point_links_checked21728 : (cuts21728.take 1).map (fun c => (2851864577-1+2*2^9*c.k,101092675048382+c.lower,101093056040620+c.upper)) = pointBounds21728 := by
 decide +kernel
def cuts21729 : List PrefixCut := [⟨18,82113149,82113197⟩,
⟨106,493065934,493066219⟩,
⟨128,595308629,595308974⟩]
theorem checked21729 : checkPrefixCuts (2^48) 2851995649 9 Manual.Count131072.C021729.packed 128 cuts21729 = true := by
 decide +kernel
def pointBounds21729 : List (Nat × Nat × Nat) := [(2852014080,101093345489924,101093726482556),(2852104192,101093756442709,101094137435578)]
theorem point_links_checked21729 : (cuts21729.take 2).map (fun c => (2851995649-1+2*2^9*c.k,101093263376775+c.lower,101093644369359+c.upper)) = pointBounds21729 := by
 decide +kernel
def cuts21730 : List PrefixCut := [⟨66,313434075,313434252⟩,
⟨128,600511699,600512044⟩]
theorem checked21730 : checkPrefixCuts (2^48) 2852126721 9 Manual.Count131072.C021730.packed 128 cuts21730 = true := by
 decide +kernel
def pointBounds21730 : List (Nat × Nat × Nat) := [(2852194304,101094172119479,101094553112585)]
theorem point_links_checked21730 : (cuts21730.take 1).map (fun c => (2852126721-1+2*2^9*c.k,101093858685404+c.lower,101094239678333+c.upper)) = pointBounds21730 := by
 decide +kernel
def cuts21731 : List PrefixCut := [⟨26,118914796,118914866⟩,
⟨114,530519388,530519695⟩,
⟨128,595845985,595846329⟩]
theorem checked21731 : checkPrefixCuts (2^48) 2852257793 9 Manual.Count131072.C021731.packed 128 cuts21731 = true := by
 decide +kernel
def pointBounds21731 : List (Nat × Nat × Nat) := [(2852284416,101094578111899,101094959105243),(2852374528,101094989716491,101095370710072)]
theorem point_links_checked21731 : (cuts21731.take 2).map (fun c => (2852257793-1+2*2^9*c.k,101094459197103+c.lower,101094840190377+c.upper)) = pointBounds21731 := by
 decide +kernel
def cuts21732 : List PrefixCut := [⟨74,343995376,343995577⟩,
⟨128,599370984,599371333⟩]
theorem checked21732 : checkPrefixCuts (2^48) 2852388865 9 Manual.Count131072.C021732.packed 128 cuts21732 = true := by
 decide +kernel
def pointBounds21732 : List (Nat × Nat × Nat) := [(2852464640,101095399038464,101095780032283)]
theorem point_links_checked21732 : (cuts21732.take 1).map (fun c => (2852388865-1+2*2^9*c.k,101095055043088+c.lower,101095436036706+c.upper)) = pointBounds21732 := by
 decide +kernel
def cuts21733 : List PrefixCut := [⟨34,157387067,157387153⟩,
⟨122,568459287,568459614⟩,
⟨128,596383306,596383649⟩]
theorem checked21733 : checkPrefixCuts (2^48) 2852519937 9 Manual.Count131072.C021733.packed 128 cuts21733 = true := by
 decide +kernel
def pointBounds21733 : List (Nat × Nat × Nat) := [(2852554752,101095811801139,101096192795192),(2852644864,101096222873359,101096603867653)]
theorem point_links_checked21733 : (cuts21733.take 2).map (fun c => (2852519937-1+2*2^9*c.k,101095654414072+c.lower,101096035408039+c.upper)) = pointBounds21733 := by
 decide +kernel
def cuts21734 : List PrefixCut := [⟨82,377313631,377313851⟩,
⟨128,593593082,593593425⟩]
theorem checked21734 : checkPrefixCuts (2^48) 2852651009 9 Manual.Count131072.C021734.packed 128 cuts21734 = true := by
 decide +kernel
def pointBounds21734 : List (Nat × Nat × Nat) := [(2852734976,101096628111009,101097009105539)]
theorem point_links_checked21734 : (cuts21734.take 1).map (fun c => (2852651009-1+2*2^9*c.k,101096250797378+c.lower,101096631791688+c.upper)) = pointBounds21734 := by
 decide +kernel
def cuts21735 : List PrefixCut := [⟨42,191017484,191017592⟩,
⟨128,588435264,588435594⟩]
theorem checked21735 : checkPrefixCuts (2^48) 2852782081 9 Manual.Count131072.C021735.packed 128 cuts21735 = true := by
 decide +kernel
def pointBounds21735 : List (Nat × Nat × Nat) := [(2852825088,101097035407944,101097416402705)]
theorem point_links_checked21735 : (cuts21735.take 1).map (fun c => (2852782081-1+2*2^9*c.k,101096844390460+c.lower,101097225385113+c.upper)) = pointBounds21735 := by
 decide +kernel
def cuts21736 : List PrefixCut := [⟨2,9570237,9570243⟩,
⟨90,421379865,421380108⟩,
⟨128,594722693,594723034⟩]
theorem checked21736 : checkPrefixCuts (2^48) 2852913153 9 Manual.Count131072.C021736.packed 128 cuts21736 = true := by
 decide +kernel
def pointBounds21736 : List (Nat × Nat × Nat) := [(2852915200,101097442395961,101097823390950),(2853005312,101097854205589,101098235200815)]
theorem point_links_checked21736 : (cuts21736.take 2).map (fun c => (2852913153-1+2*2^9*c.k,101097432825724+c.lower,101097813820707+c.upper)) = pointBounds21736 := by
 decide +kernel
def cuts21737 : List PrefixCut := [⟨50,228982573,228982701⟩,
⟨128,589861066,589861402⟩]
theorem checked21737 : checkPrefixCuts (2^48) 2853044225 9 Manual.Count131072.C021737.packed 128 cuts21737 = true := by
 decide +kernel
def pointBounds21737 : List (Nat × Nat × Nat) := [(2853095424,101098256530990,101098637526442)]
theorem point_links_checked21737 : (cuts21737.take 1).map (fun c => (2853044225-1+2*2^9*c.k,101098027548417+c.lower,101098408543741+c.upper)) = pointBounds21737 := by
 decide +kernel
def cuts21738 : List PrefixCut := [⟨10,42815413,42815438⟩,
⟨98,451527751,451528020⟩,
⟨128,591708275,591708627⟩]
theorem checked21738 : checkPrefixCuts (2^48) 2853175297 9 Manual.Count131072.C021738.packed 128 cuts21738 = true := by
 decide +kernel
def pointBounds21738 : List (Nat × Nat × Nat) := [(2853185536,101098660224896,101099041220581),(2853275648,101099068937234,101099449933163)]
theorem point_links_checked21738 : (cuts21738.take 2).map (fun c => (2853175297-1+2*2^9*c.k,101098617409483+c.lower,101098998405143+c.upper)) = pointBounds21738 := by
 decide +kernel
def cuts21739 : List PrefixCut := [⟨58,267335132,267335289⟩,
⟨128,590497371,590497718⟩]
theorem checked21739 : checkPrefixCuts (2^48) 2853306369 9 Manual.Count131072.C021739.packed 128 cuts21739 = true := by
 decide +kernel
def pointBounds21739 : List (Nat × Nat × Nat) := [(2853365760,101099476452890,101099857449059)]
theorem point_links_checked21739 : (cuts21739.take 1).map (fun c => (2853306369-1+2*2^9*c.k,101099209117758+c.lower,101099590113770+c.upper)) = pointBounds21739 := by
 decide +kernel
def cuts21740 : List PrefixCut := [⟨18,85326915,85326962⟩,
⟨106,500313565,500313848⟩,
⟨128,601419577,601419918⟩]
theorem checked21740 : checkPrefixCuts (2^48) 2853437441 9 Manual.Count131072.C021740.packed 128 cuts21740 = true := by
 decide +kernel
def pointBounds21740 : List (Nat × Nat × Nat) := [(2853455872,101099884942044,101100265938450),(2853545984,101100299928694,101100680925336)]
theorem point_links_checked21740 : (cuts21740.take 2).map (fun c => (2853437441-1+2*2^9*c.k,101099799615129+c.lower,101100180611488+c.upper)) = pointBounds21740 := by
 decide +kernel
def cuts21741 : List PrefixCut := [⟨66,305483279,305483454⟩,
⟨128,595079085,595079428⟩]
theorem checked21741 : checkPrefixCuts (2^48) 2853568513 9 Manual.Count131072.C021741.packed 128 cuts21741 = true := by
 decide +kernel
def pointBounds21741 : List (Nat × Nat × Nat) := [(2853636096,101100706517985,101101087514860)]
theorem point_links_checked21741 : (cuts21741.take 1).map (fun c => (2853568513-1+2*2^9*c.k,101100401034706+c.lower,101100782031406+c.upper)) = pointBounds21741 := by
 decide +kernel
def cuts21742 : List PrefixCut := [⟨26,122800106,122800174⟩,
⟨114,540016055,540016361⟩,
⟨128,606493213,606493557⟩]
theorem checked21742 : checkPrefixCuts (2^48) 2853699585 9 Manual.Count131072.C021742.packed 128 cuts21742 = true := by
 decide +kernel
def pointBounds21742 : List (Nat × Nat × Nat) := [(2853726208,101101118913897,101101499911008),(2853816320,101101536129846,101101917127195)]
theorem point_links_checked21742 : (cuts21742.take 2).map (fun c => (2853699585-1+2*2^9*c.k,101100996113791+c.lower,101101377110834+c.upper)) = pointBounds21742 := by
 decide +kernel
def cuts21743 : List PrefixCut := [⟨74,347766708,347766908⟩,
⟨128,598870989,598871333⟩]
theorem checked21743 : checkPrefixCuts (2^48) 2853830657 9 Manual.Count131072.C021743.packed 128 cuts21743 = true := by
 decide +kernel
def pointBounds21743 : List (Nat × Nat × Nat) := [(2853906432,101101950373712,101102331371299)]
theorem point_links_checked21743 : (cuts21743.take 1).map (fun c => (2853830657-1+2*2^9*c.k,101101602607004+c.lower,101101983604391+c.upper)) = pointBounds21743 := by
 decide +kernel
def cuts21744 : List PrefixCut := [⟨34,158195162,158195254⟩,
⟨122,572215646,572215972⟩,
⟨128,597660018,597660359⟩]
theorem checked21744 : checkPrefixCuts (2^48) 2853961729 9 Manual.Count131072.C021744.packed 128 cuts21744 = true := by
 decide +kernel
def pointBounds21744 : List (Nat × Nat × Nat) := [(2853996544,101102359673155,101102740670978),(2854086656,101102773693639,101103154691696)]
theorem point_links_checked21744 : (cuts21744.take 2).map (fun c => (2853961729-1+2*2^9*c.k,101102201477993+c.lower,101102582475724+c.upper)) = pointBounds21744 := by
 decide +kernel
def cuts21745 : List PrefixCut := [⟨82,380574771,380574987⟩,
⟨128,588066600,588066935⟩]
theorem checked21745 : checkPrefixCuts (2^48) 2854092801 9 Manual.Count131072.C021745.packed 128 cuts21745 = true := by
 decide +kernel
def pointBounds21745 : List (Nat × Nat × Nat) := [(2854176768,101103179712782,101103560711070)]
theorem point_links_checked21745 : (cuts21745.take 1).map (fun c => (2854092801-1+2*2^9*c.k,101102799138011+c.lower,101103180136083+c.upper)) = pointBounds21745 := by
 decide +kernel
def cuts21746 : List PrefixCut := [⟨42,194471161,194471274⟩,
⟨128,593956369,593956709⟩]
theorem checked21746 : checkPrefixCuts (2^48) 2854223873 9 Manual.Count131072.C021746.packed 128 cuts21746 = true := by
 decide +kernel
def pointBounds21746 : List (Nat × Nat × Nat) := [(2854266880,101103581675772,101103962674292)]
theorem point_links_checked21746 : (cuts21746.take 1).map (fun c => (2854223873-1+2*2^9*c.k,101103387204611+c.lower,101103768203018+c.upper)) = pointBounds21746 := by
 decide +kernel
def cuts21747 : List PrefixCut := [⟨2,8579278,8579284⟩,
⟨90,411601617,411601854⟩,
⟨128,586533239,586533575⟩]
theorem checked21747 : checkPrefixCuts (2^48) 2854354945 9 Manual.Count131072.C021747.packed 128 cuts21747 = true := by
 decide +kernel
def pointBounds21747 : List (Nat × Nat × Nat) := [(2854356992,101103989740258,101104370739011),(2854447104,101104392762597,101104773761581)]
theorem point_links_checked21747 : (cuts21747.take 2).map (fun c => (2854354945-1+2*2^9*c.k,101103981160980+c.lower,101104362159727+c.upper)) = pointBounds21747 := by
 decide +kernel
def cuts21748 : List PrefixCut := [⟨50,233797261,233797395⟩,
⟨128,595676734,595677071⟩]
theorem checked21748 : checkPrefixCuts (2^48) 2854486017 9 Manual.Count131072.C021748.packed 128 cuts21748 = true := by
 decide +kernel
def pointBounds21748 : List (Nat × Nat × Nat) := [(2854537216,101104801491480,101105182490697)]
theorem point_links_checked21748 : (cuts21748.take 1).map (fun c => (2854486017-1+2*2^9*c.k,101104567694219+c.lower,101104948693302+c.upper)) = pointBounds21748 := by
 decide +kernel
def cuts21749 : List PrefixCut := [⟨10,46047696,46047721⟩,
⟨98,463033248,463033516⟩,
⟨128,601466794,601467138⟩]
theorem checked21749 : checkPrefixCuts (2^48) 2854617089 9 Manual.Count131072.C021749.packed 128 cuts21749 = true := by
 decide +kernel
def pointBounds21749 : List (Nat × Nat × Nat) := [(2854627328,101105209418649,101105590418094),(2854717440,101105626404201,101106007403889)]
theorem point_links_checked21749 : (cuts21749.take 2).map (fun c => (2854617089-1+2*2^9*c.k,101105163370953+c.lower,101105544370373+c.upper)) = pointBounds21749 := by
 decide +kernel
def cuts21750 : List PrefixCut := [⟨58,264735186,264735336⟩,
⟨128,586649698,586650029⟩]
theorem checked21750 : checkPrefixCuts (2^48) 2854748161 9 Manual.Count131072.C021750.packed 128 cuts21750 = true := by
 decide +kernel
def pointBounds21750 : List (Nat × Nat × Nat) := [(2854807552,101106029572933,101106410572847)]
theorem point_links_checked21750 : (cuts21750.take 1).map (fun c => (2854748161-1+2*2^9*c.k,101105764837747+c.lower,101106145837511+c.upper)) = pointBounds21750 := by
 decide +kernel
def cuts21751 : List PrefixCut := [⟨18,84889447,84889497⟩,
⟨106,490891906,490892190⟩,
⟨128,595594684,595595027⟩]
theorem checked21751 : checkPrefixCuts (2^48) 2854879233 9 Manual.Count131072.C021751.packed 128 cuts21751 = true := by
 decide +kernel
def pointBounds21751 : List (Nat × Nat × Nat) := [(2854897664,101106436376892,101106817377037),(2854987776,101106842379351,101107223379730)]
theorem point_links_checked21751 : (cuts21751.take 2).map (fun c => (2854879233-1+2*2^9*c.k,101106351487445+c.lower,101106732487540+c.upper)) = pointBounds21751 := by
 decide +kernel
def cuts21752 : List PrefixCut := [⟨66,305427583,305427755⟩,
⟨128,594187074,594187408⟩]
theorem checked21752 : checkPrefixCuts (2^48) 2855010305 9 Manual.Count131072.C021752.packed 128 cuts21752 = true := by
 decide +kernel
def pointBounds21752 : List (Nat × Nat × Nat) := [(2855077888,101107252509712,101107633510322)]
theorem point_links_checked21752 : (cuts21752.take 1).map (fun c => (2855010305-1+2*2^9*c.k,101106947082129+c.lower,101107328082567+c.upper)) = pointBounds21752 := by
 decide +kernel
def cuts21753 : List PrefixCut := [⟨26,122935266,122935337⟩,
⟨114,529096344,529096654⟩,
⟨128,594849862,594850209⟩]
theorem checked21753 : checkPrefixCuts (2^48) 2855141377 9 Manual.Count131072.C021753.packed 128 cuts21753 = true := by
 decide +kernel
def pointBounds21753 : List (Nat × Nat × Nat) := [(2855168000,101107664204469,101108045205312),(2855258112,101108070365547,101108451366629)]
theorem point_links_checked21753 : (cuts21753.take 2).map (fun c => (2855141377-1+2*2^9*c.k,101107541269203+c.lower,101107922269975+c.upper)) = pointBounds21753 := by
 decide +kernel
def cuts21754 : List PrefixCut := [⟨74,340789220,340789416⟩,
⟨128,588415101,588415435⟩]
theorem checked21754 : checkPrefixCuts (2^48) 2855272449 9 Manual.Count131072.C021754.packed 128 cuts21754 = true := by
 decide +kernel
def pointBounds21754 : List (Nat × Nat × Nat) := [(2855348224,101108476908285,101108857909600)]
theorem point_links_checked21754 : (cuts21754.take 1).map (fun c => (2855272449-1+2*2^9*c.k,101108136119065+c.lower,101108517120184+c.upper)) = pointBounds21754 := by
 decide +kernel
def cuts21755 : List PrefixCut := [⟨34,156045226,156045315⟩,
⟨122,559703505,559703825⟩,
⟨128,587599328,587599664⟩]
theorem checked21755 : checkPrefixCuts (2^48) 2855403521 9 Manual.Count131072.C021755.packed 128 cuts21755 = true := by
 decide +kernel
def pointBounds21755 : List (Nat × Nat × Nat) := [(2855438336,101108880579392,101109261580934),(2855528448,101109284237671,101109665239444)]
theorem point_links_checked21755 : (cuts21755.take 2).map (fun c => (2855403521-1+2*2^9*c.k,101108724534166+c.lower,101109105535619+c.upper)) = pointBounds21755 := by
 decide +kernel
def cuts21756 : List PrefixCut := [⟨82,377228349,377228570⟩,
⟨128,586685337,586685677⟩]
theorem checked21756 : checkPrefixCuts (2^48) 2855534593 9 Manual.Count131072.C021756.packed 128 cuts21756 = true := by
 decide +kernel
def pointBounds21756 : List (Nat × Nat × Nat) := [(2855618560,101109689361843,101110070363853)]
theorem point_links_checked21756 : (cuts21756.take 1).map (fun c => (2855534593-1+2*2^9*c.k,101109312133494+c.lower,101109693135283+c.upper)) = pointBounds21756 := by
 decide +kernel
def cuts21757 : List PrefixCut := [⟨42,195950073,195950183⟩,
⟨128,593262230,593262566⟩]
theorem checked21757 : checkPrefixCuts (2^48) 2855665665 9 Manual.Count131072.C021757.packed 128 cuts21757 = true := by
 decide +kernel
def pointBounds21757 : List (Nat × Nat × Nat) := [(2855708672,101110094768904,101110475771143)]
theorem point_links_checked21757 : (cuts21757.take 1).map (fun c => (2855665665-1+2*2^9*c.k,101109898818831+c.lower,101110279820960+c.upper)) = pointBounds21757 := by
 decide +kernel
def cuts21758 : List PrefixCut := [⟨2,7589321,7589326⟩,
⟨90,417800300,417800545⟩,
⟨128,595107594,595107942⟩]
theorem checked21758 : checkPrefixCuts (2^48) 2855796737 9 Manual.Count131072.C021758.packed 128 cuts21758 = true := by
 decide +kernel
def pointBounds21758 : List (Nat × Nat × Nat) := [(2855798784,101110499670382,101110880672852),(2855888896,101110909881361,101111290884071)]
theorem point_links_checked21758 : (cuts21758.take 2).map (fun c => (2855796737-1+2*2^9*c.k,101110492081061+c.lower,101110873083526+c.upper)) = pointBounds21758 := by
 decide +kernel
def cuts21759 : List PrefixCut := [⟨50,227864354,227864490⟩,
⟨128,592714933,592715280⟩]
theorem checked21759 : checkPrefixCuts (2^48) 2855927809 9 Manual.Count131072.C021759.packed 128 cuts21759 = true := by
 decide +kernel
def pointBounds21759 : List (Nat × Nat × Nat) := [(2855979008,101111315053009,101111696055958)]
theorem point_links_checked21759 : (cuts21759.take 1).map (fun c => (2855927809-1+2*2^9*c.k,101111087188655+c.lower,101111468191468+c.upper)) = pointBounds21759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000054
