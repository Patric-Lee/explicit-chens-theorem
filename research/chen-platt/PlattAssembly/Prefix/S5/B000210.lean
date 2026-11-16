import PlattAssemblyKernel
import PlattCertificates.Count131072.C046720
import PlattCertificates.Count131072.C046721
import PlattCertificates.Count131072.C046722
import PlattCertificates.Count131072.C046723
import PlattCertificates.Count131072.C046724
import PlattCertificates.Count131072.C046725
import PlattCertificates.Count131072.C046726
import PlattCertificates.Count131072.C046727
import PlattCertificates.Count131072.C046728
import PlattCertificates.Count131072.C046729
import PlattCertificates.Count131072.C046730
import PlattCertificates.Count131072.C046731
import PlattCertificates.Count131072.C046732
import PlattCertificates.Count131072.C046733
import PlattCertificates.Count131072.C046734
import PlattCertificates.Count131072.C046735
import PlattCertificates.Count131072.C046736
import PlattCertificates.Count131072.C046737
import PlattCertificates.Count131072.C046738
import PlattCertificates.Count131072.C046739
import PlattCertificates.Count131072.C046740
import PlattCertificates.Count131072.C046741
import PlattCertificates.Count131072.C046742
import PlattCertificates.Count131072.C046743
import PlattCertificates.Count131072.C046744
import PlattCertificates.Count131072.C046745
import PlattCertificates.Count131072.C046746
import PlattCertificates.Count131072.C046747
import PlattCertificates.Count131072.C046748
import PlattCertificates.Count131072.C046749
import PlattCertificates.Count131072.C046750
import PlattCertificates.Count131072.C046751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46720 : List PrefixCut := [⟨22,92513687,92513741⟩,
⟨64,266744404,266744557⟩]
theorem checked46720 : checkPrefixCuts (2^48) 6127616001 10 Manual.Count131072.C046720.packed 64 cuts46720 = true := by
 decide +kernel
def pointBounds46720 : List (Nat × Nat × Nat) := [(6127661056,110811322744667,110811709383472)]
theorem point_links_checked46720 : (cuts46720.take 1).map (fun c => (6127616001-1+2*2^10*c.k,110811230230980+c.lower,110811616869731+c.upper)) = pointBounds46720 := by
 decide +kernel
def cuts46721 : List PrefixCut := [⟨52,217268223,217268344⟩,
⟨64,267335838,267335988⟩]
theorem checked46721 : checkPrefixCuts (2^48) 6127747073 10 Manual.Count131072.C046721.packed 64 cuts46721 = true := by
 decide +kernel
def pointBounds46721 : List (Nat × Nat × Nat) := [(6127853568,110811714243607,110812100882632)]
theorem point_links_checked46721 : (cuts46721.take 1).map (fun c => (6127747073-1+2*2^10*c.k,110811496975384+c.lower,110811883614288+c.upper)) = pointBounds46721 := by
 decide +kernel
def cuts46722 : List PrefixCut := [⟨64,266595205,266595356⟩]
theorem checked46722 : checkPrefixCuts (2^48) 6127878145 10 Manual.Count131072.C046722.packed 64 cuts46722 = true := by
 decide +kernel
def cuts46723 : List PrefixCut := [⟨18,72297564,72297609⟩,
⟨64,264476599,264476754⟩]
theorem checked46723 : checkPrefixCuts (2^48) 6128009217 10 Manual.Count131072.C046723.packed 64 cuts46723 = true := by
 decide +kernel
def pointBounds46723 : List (Nat × Nat × Nat) := [(6128046080,110812103203991,110812489843241)]
theorem point_links_checked46723 : (cuts46723.take 1).map (fun c => (6128009217-1+2*2^10*c.k,110812030906427+c.lower,110812417545632+c.upper)) = pointBounds46723 := by
 decide +kernel
def cuts46724 : List PrefixCut := [⟨48,197641814,197641926⟩,
⟨64,266124454,266124605⟩]
theorem checked46724 : checkPrefixCuts (2^48) 6128140289 10 Manual.Count131072.C046724.packed 64 cuts46724 = true := by
 decide +kernel
def pointBounds46724 : List (Nat × Nat × Nat) := [(6128238592,110812493024840,110812879664312)]
theorem point_links_checked46724 : (cuts46724.take 1).map (fun c => (6128140289-1+2*2^10*c.k,110812295383026+c.lower,110812682022386+c.upper)) = pointBounds46724 := by
 decide +kernel
def cuts46725 : List PrefixCut := [⟨64,267312975,267313135⟩]
theorem checked46725 : checkPrefixCuts (2^48) 6128271361 10 Manual.Count131072.C046725.packed 64 cuts46725 = true := by
 decide +kernel
def cuts46726 : List PrefixCut := [⟨14,57319968,57320003⟩,
⟨64,268593236,268593395⟩]
theorem checked46726 : checkPrefixCuts (2^48) 6128402433 10 Manual.Count131072.C046726.packed 64 cuts46726 = true := by
 decide +kernel
def pointBounds46726 : List (Nat × Nat × Nat) := [(6128431104,110812886140423,110813272780129)]
theorem point_links_checked46726 : (cuts46726.take 1).map (fun c => (6128402433-1+2*2^10*c.k,110812828820455+c.lower,110813215460126+c.upper)) = pointBounds46726 := by
 decide +kernel
def cuts46727 : List PrefixCut := [⟨44,180819529,180819633⟩,
⟨64,263948770,263948924⟩]
theorem checked46727 : checkPrefixCuts (2^48) 6128533505 10 Manual.Count131072.C046727.packed 64 cuts46727 = true := by
 decide +kernel
def pointBounds46727 : List (Nat × Nat × Nat) := [(6128623616,110813278233220,110813664873154)]
theorem point_links_checked46727 : (cuts46727.take 1).map (fun c => (6128533505-1+2*2^10*c.k,110813097413691+c.lower,110813484053521+c.upper)) = pointBounds46727 := by
 decide +kernel
def cuts46728 : List PrefixCut := [⟨64,267801002,267801157⟩]
theorem checked46728 : checkPrefixCuts (2^48) 6128664577 10 Manual.Count131072.C046728.packed 64 cuts46728 = true := by
 decide +kernel
def cuts46729 : List PrefixCut := [⟨10,42068720,42068742⟩,
⟨64,265820477,265820629⟩]
theorem checked46729 : checkPrefixCuts (2^48) 6128795649 10 Manual.Count131072.C046729.packed 64 cuts46729 = true := by
 decide +kernel
def pointBounds46729 : List (Nat × Nat × Nat) := [(6128816128,110813671232183,110814057872344)]
theorem point_links_checked46729 : (cuts46729.take 1).map (fun c => (6128795649-1+2*2^10*c.k,110813629163463+c.lower,110814015803602+c.upper)) = pointBounds46729 := by
 decide +kernel
def cuts46730 : List PrefixCut := [⟨40,167351926,167352022⟩,
⟨64,268478436,268478589⟩]
theorem checked46730 : checkPrefixCuts (2^48) 6128926721 10 Manual.Count131072.C046730.packed 64 cuts46730 = true := by
 decide +kernel
def pointBounds46730 : List (Nat × Nat × Nat) := [(6129008640,110814062335866,110814448976253)]
theorem point_links_checked46730 : (cuts46730.take 1).map (fun c => (6128926721-1+2*2^10*c.k,110813894983940+c.lower,110814281624231+c.upper)) = pointBounds46730 := by
 decide +kernel
def cuts46731 : List PrefixCut := [⟨64,268105292,268105442⟩]
theorem checked46731 : checkPrefixCuts (2^48) 6129057793 10 Manual.Count131072.C046731.packed 64 cuts46731 = true := by
 decide +kernel
def cuts46732 : List PrefixCut := [⟨6,25120229,25120243⟩,
⟨64,267135182,267135331⟩]
theorem checked46732 : checkPrefixCuts (2^48) 6129188865 10 Manual.Count131072.C046732.packed 64 cuts46732 = true := by
 decide +kernel
def pointBounds46732 : List (Nat × Nat × Nat) := [(6129201152,110814456687897,110814843328505)]
theorem point_links_checked46732 : (cuts46732.take 1).map (fun c => (6129188865-1+2*2^10*c.k,110814431567668+c.lower,110814818208262+c.upper)) = pointBounds46732 := by
 decide +kernel
def cuts46733 : List PrefixCut := [⟨36,152232824,152232911⟩,
⟨64,269884809,269884960⟩]
theorem checked46733 : checkPrefixCuts (2^48) 6129319937 10 Manual.Count131072.C046733.packed 64 cuts46733 = true := by
 decide +kernel
def pointBounds46733 : List (Nat × Nat × Nat) := [(6129393664,110814850935674,110815237576504)]
theorem point_links_checked46733 : (cuts46733.take 1).map (fun c => (6129319937-1+2*2^10*c.k,110814698702850+c.lower,110815085343593+c.upper)) = pointBounds46733 := by
 decide +kernel
def cuts46734 : List PrefixCut := [⟨64,263817425,263817584⟩]
theorem checked46734 : checkPrefixCuts (2^48) 6129451009 10 Manual.Count131072.C046734.packed 64 cuts46734 = true := by
 decide +kernel
def cuts46735 : List PrefixCut := [⟨2,8173887,8173893⟩,
⟨64,271618222,271618382⟩]
theorem checked46735 : checkPrefixCuts (2^48) 6129582081 10 Manual.Count131072.C046735.packed 64 cuts46735 = true := by
 decide +kernel
def pointBounds46735 : List (Nat × Nat × Nat) := [(6129586176,110815240578971,110815627220030)]
theorem point_links_checked46735 : (cuts46735.take 1).map (fun c => (6129582081-1+2*2^10*c.k,110815232405084+c.lower,110815619046137+c.upper)) = pointBounds46735 := by
 decide +kernel
def cuts46736 : List PrefixCut := [⟨32,130962420,130962500⟩,
⟨64,264770418,264770575⟩]
theorem checked46736 : checkPrefixCuts (2^48) 6129713153 10 Manual.Count131072.C046736.packed 64 cuts46736 = true := by
 decide +kernel
def pointBounds46736 : List (Nat × Nat × Nat) := [(6129778688,110815634985726,110816021627019)]
theorem point_links_checked46736 : (cuts46736.take 1).map (fun c => (6129713153-1+2*2^10*c.k,110815504023306+c.lower,110815890664519+c.upper)) = pointBounds46736 := by
 decide +kernel
def cuts46737 : List PrefixCut := [⟨62,260356706,260356856⟩,
⟨64,268943335,268943490⟩]
theorem checked46737 : checkPrefixCuts (2^48) 6129844225 10 Manual.Count131072.C046737.packed 64 cuts46737 = true := by
 decide +kernel
def pointBounds46737 : List (Nat × Nat × Nat) := [(6129971200,110816029150430,110816415791950)]
theorem point_links_checked46737 : (cuts46737.take 1).map (fun c => (6129844225-1+2*2^10*c.k,110815768793724+c.lower,110816155435094+c.upper)) = pointBounds46737 := by
 decide +kernel
def cuts46738 : List PrefixCut := [⟨64,261590821,261590969⟩]
theorem checked46738 : checkPrefixCuts (2^48) 6129975297 10 Manual.Count131072.C046738.packed 64 cuts46738 = true := by
 decide +kernel
def cuts46739 : List PrefixCut := [⟨28,117592386,117592454⟩,
⟨64,267095213,267095370⟩]
theorem checked46739 : checkPrefixCuts (2^48) 6130106369 10 Manual.Count131072.C046739.packed 64 cuts46739 = true := by
 decide +kernel
def pointBounds46739 : List (Nat × Nat × Nat) := [(6130163712,110816416920266,110816803562007)]
theorem point_links_checked46739 : (cuts46739.take 1).map (fun c => (6130106369-1+2*2^10*c.k,110816299327880+c.lower,110816685969553+c.upper)) = pointBounds46739 := by
 decide +kernel
def cuts46740 : List PrefixCut := [⟨58,239402791,239402924⟩,
⟨64,264931468,264931617⟩]
theorem checked46740 : checkPrefixCuts (2^48) 6130237441 10 Manual.Count131072.C046740.packed 64 cuts46740 = true := by
 decide +kernel
def pointBounds46740 : List (Nat × Nat × Nat) := [(6130356224,110816805825884,110817192467847)]
theorem point_links_checked46740 : (cuts46740.take 1).map (fun c => (6130237441-1+2*2^10*c.k,110816566423093+c.lower,110816953064923+c.upper)) = pointBounds46740 := by
 decide +kernel
def cuts46741 : List PrefixCut := [⟨64,269149919,269150077⟩]
theorem checked46741 : checkPrefixCuts (2^48) 6130368513 10 Manual.Count131072.C046741.packed 64 cuts46741 = true := by
 decide +kernel
def cuts46742 : List PrefixCut := [⟨24,98806231,98806288⟩,
⟨64,265425181,265425335⟩]
theorem checked46742 : checkPrefixCuts (2^48) 6130499585 10 Manual.Count131072.C046742.packed 64 cuts46742 = true := by
 decide +kernel
def pointBounds46742 : List (Nat × Nat × Nat) := [(6130548736,110817199310711,110817585952905)]
theorem point_links_checked46742 : (cuts46742.take 1).map (fun c => (6130499585-1+2*2^10*c.k,110817100504480+c.lower,110817487146617+c.upper)) = pointBounds46742 := by
 decide +kernel
def cuts46743 : List PrefixCut := [⟨54,223547798,223547929⟩,
⟨64,266337756,266337913⟩]
theorem checked46743 : checkPrefixCuts (2^48) 6130630657 10 Manual.Count131072.C046743.packed 64 cuts46743 = true := by
 decide +kernel
def pointBounds46743 : List (Nat × Nat × Nat) := [(6130741248,110817589477459,110817976119881)]
theorem point_links_checked46743 : (cuts46743.take 1).map (fun c => (6130630657-1+2*2^10*c.k,110817365929661+c.lower,110817752571952+c.upper)) = pointBounds46743 := by
 decide +kernel
def cuts46744 : List PrefixCut := [⟨64,271152747,271152906⟩]
theorem checked46744 : checkPrefixCuts (2^48) 6130761729 10 Manual.Count131072.C046744.packed 64 cuts46744 = true := by
 decide +kernel
def cuts46745 : List PrefixCut := [⟨20,83282120,83282169⟩,
⟨64,268116875,268117031⟩]
theorem checked46745 : checkPrefixCuts (2^48) 6130892801 10 Manual.Count131072.C046745.packed 64 cuts46745 = true := by
 decide +kernel
def pointBounds46745 : List (Nat × Nat × Nat) := [(6130933760,110817986702284,110818373344940)]
theorem point_links_checked46745 : (cuts46745.take 1).map (fun c => (6130892801-1+2*2^10*c.k,110817903420164+c.lower,110818290062771+c.upper)) = pointBounds46745 := by
 decide +kernel
def cuts46746 : List PrefixCut := [⟨50,208062052,208062172⟩,
⟨64,266320648,266320801⟩]
theorem checked46746 : checkPrefixCuts (2^48) 6131023873 10 Manual.Count131072.C046746.packed 64 cuts46746 = true := by
 decide +kernel
def pointBounds46746 : List (Nat × Nat × Nat) := [(6131126272,110818379599091,110818766241974)]
theorem point_links_checked46746 : (cuts46746.take 1).map (fun c => (6131023873-1+2*2^10*c.k,110818171537039+c.lower,110818558179802+c.upper)) = pointBounds46746 := by
 decide +kernel
def cuts46747 : List PrefixCut := [⟨64,268702229,268702380⟩]
theorem checked46747 : checkPrefixCuts (2^48) 6131154945 10 Manual.Count131072.C046747.packed 64 cuts46747 = true := by
 decide +kernel
def cuts46748 : List PrefixCut := [⟨16,67071365,67071404⟩,
⟨64,267732412,267732567⟩]
theorem checked46748 : checkPrefixCuts (2^48) 6131286017 10 Manual.Count131072.C046748.packed 64 cuts46748 = true := by
 decide +kernel
def pointBounds46748 : List (Nat × Nat × Nat) := [(6131318784,110818773631281,110819160274387)]
theorem point_links_checked46748 : (cuts46748.take 1).map (fun c => (6131286017-1+2*2^10*c.k,110818706559916+c.lower,110819093202983+c.upper)) = pointBounds46748 := by
 decide +kernel
def cuts46749 : List PrefixCut := [⟨46,194139153,194139264⟩,
⟨64,268644827,268644982⟩]
theorem checked46749 : checkPrefixCuts (2^48) 6131417089 10 Manual.Count131072.C046749.packed 64 cuts46749 = true := by
 decide +kernel
def pointBounds46749 : List (Nat × Nat × Nat) := [(6131511296,110819168431481,110819555074814)]
theorem point_links_checked46749 : (cuts46749.take 1).map (fun c => (6131417089-1+2*2^10*c.k,110818974292328+c.lower,110819360935550+c.upper)) = pointBounds46749 := by
 decide +kernel
def cuts46750 : List PrefixCut := [⟨64,266297896,266298049⟩]
theorem checked46750 : checkPrefixCuts (2^48) 6131548161 10 Manual.Count131072.C046750.packed 64 cuts46750 = true := by
 decide +kernel
def cuts46751 : List PrefixCut := [⟨12,50908572,50908599⟩,
⟨64,266613576,266613728⟩]
theorem checked46751 : checkPrefixCuts (2^48) 6131679233 10 Manual.Count131072.C046751.packed 64 cuts46751 = true := by
 decide +kernel
def pointBounds46751 : List (Nat × Nat × Nat) := [(6131703808,110819560143623,110819946787180)]
theorem point_links_checked46751 : (cuts46751.take 1).map (fun c => (6131679233-1+2*2^10*c.k,110819509235051+c.lower,110819895878581+c.upper)) = pointBounds46751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000210
