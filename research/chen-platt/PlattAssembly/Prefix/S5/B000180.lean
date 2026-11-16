import PlattAssemblyKernel
import PlattCertificates.Count131072.C045760
import PlattCertificates.Count131072.C045761
import PlattCertificates.Count131072.C045762
import PlattCertificates.Count131072.C045763
import PlattCertificates.Count131072.C045764
import PlattCertificates.Count131072.C045765
import PlattCertificates.Count131072.C045766
import PlattCertificates.Count131072.C045767
import PlattCertificates.Count131072.C045768
import PlattCertificates.Count131072.C045769
import PlattCertificates.Count131072.C045770
import PlattCertificates.Count131072.C045771
import PlattCertificates.Count131072.C045772
import PlattCertificates.Count131072.C045773
import PlattCertificates.Count131072.C045774
import PlattCertificates.Count131072.C045775
import PlattCertificates.Count131072.C045776
import PlattCertificates.Count131072.C045777
import PlattCertificates.Count131072.C045778
import PlattCertificates.Count131072.C045779
import PlattCertificates.Count131072.C045780
import PlattCertificates.Count131072.C045781
import PlattCertificates.Count131072.C045782
import PlattCertificates.Count131072.C045783
import PlattCertificates.Count131072.C045784
import PlattCertificates.Count131072.C045785
import PlattCertificates.Count131072.C045786
import PlattCertificates.Count131072.C045787
import PlattCertificates.Count131072.C045788
import PlattCertificates.Count131072.C045789
import PlattCertificates.Count131072.C045790
import PlattCertificates.Count131072.C045791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45760 : List PrefixCut := [⟨58,250201110,250201254⟩,
⟨64,275197499,275197657⟩]
theorem checked45760 : checkPrefixCuts (2^48) 6001786881 10 Manual.Count131072.C045760.packed 64 cuts45760 = true := by
 decide +kernel
def pointBounds45760 : List (Nat × Nat × Nat) := [(6001905664,110552183126713,110552569616771)]
theorem point_links_checked45760 : (cuts45760.take 1).map (fun c => (6001786881-1+2*2^10*c.k,110551932925603+c.lower,110552319415517+c.upper)) = pointBounds45760 := by
 decide +kernel
def cuts45761 : List PrefixCut := [⟨64,269798340,269798496⟩]
theorem checked45761 : checkPrefixCuts (2^48) 6001917953 10 Manual.Count131072.C045761.packed 64 cuts45761 = true := by
 decide +kernel
def cuts45762 : List PrefixCut := [⟨22,92385700,92385751⟩,
⟨64,271433791,271433948⟩]
theorem checked45762 : checkPrefixCuts (2^48) 6002049025 10 Manual.Count131072.C045762.packed 64 cuts45762 = true := by
 decide +kernel
def pointBounds45762 : List (Nat × Nat × Nat) := [(6002094080,110552570307142,110552956797421)]
theorem point_links_checked45762 : (cuts45762.take 1).map (fun c => (6002049025-1+2*2^10*c.k,110552477921442+c.lower,110552864411670+c.upper)) = pointBounds45762 := by
 decide +kernel
def cuts45763 : List PrefixCut := [⟨50,214404134,214404256⟩,
⟨64,274476031,274476186⟩]
theorem checked45763 : checkPrefixCuts (2^48) 6002180097 10 Manual.Count131072.C045763.packed 64 cuts45763 = true := by
 decide +kernel
def pointBounds45763 : List (Nat × Nat × Nat) := [(6002282496,110552963759367,110553350249874)]
theorem point_links_checked45763 : (cuts45763.take 1).map (fun c => (6002180097-1+2*2^10*c.k,110552749355233+c.lower,110553135845618+c.upper)) = pointBounds45763 := by
 decide +kernel
def cuts45764 : List PrefixCut := [⟨64,272453604,272453759⟩]
theorem checked45764 : checkPrefixCuts (2^48) 6002311169 10 Manual.Count131072.C045764.packed 64 cuts45764 = true := by
 decide +kernel
def cuts45765 : List PrefixCut := [⟨14,56693979,56694011⟩,
⟨64,271228396,271228551⟩]
theorem checked45765 : checkPrefixCuts (2^48) 6002442241 10 Manual.Count131072.C045765.packed 64 cuts45765 = true := by
 decide +kernel
def pointBounds45765 : List (Nat × Nat × Nat) := [(6002470912,110553352978847,110553739469574)]
theorem point_links_checked45765 : (cuts45765.take 1).map (fun c => (6002442241-1+2*2^10*c.k,110553296284868+c.lower,110553682775563+c.upper)) = pointBounds45765 := by
 decide +kernel
def cuts45766 : List PrefixCut := [⟨42,178611753,178611858⟩,
⟨64,272441696,272441855⟩]
theorem checked45766 : checkPrefixCuts (2^48) 6002573313 10 Manual.Count131072.C045766.packed 64 cuts45766 = true := by
 decide +kernel
def pointBounds45766 : List (Nat × Nat × Nat) := [(6002659328,110553746125017,110554132615972)]
theorem point_links_checked45766 : (cuts45766.take 1).map (fun c => (6002573313-1+2*2^10*c.k,110553567513264+c.lower,110553954004114+c.upper)) = pointBounds45766 := by
 decide +kernel
def cuts45767 : List PrefixCut := [⟨64,274874062,274874213⟩]
theorem checked45767 : checkPrefixCuts (2^48) 6002704385 10 Manual.Count131072.C045767.packed 64 cuts45767 = true := by
 decide +kernel
def cuts45768 : List PrefixCut := [⟨6,25273859,25273873⟩,
⟨64,271820219,271820378⟩]
theorem checked45768 : checkPrefixCuts (2^48) 6002835457 10 Manual.Count131072.C045768.packed 64 cuts45768 = true := by
 decide +kernel
def pointBounds45768 : List (Nat × Nat × Nat) := [(6002847744,110554140102881,110554526594055)]
theorem point_links_checked45768 : (cuts45768.take 1).map (fun c => (6002835457-1+2*2^10*c.k,110554114829022+c.lower,110554501320182+c.upper)) = pointBounds45768 := by
 decide +kernel
def cuts45769 : List PrefixCut := [⟨34,145121534,145121616⟩,
⟨64,275659170,275659325⟩]
theorem checked45769 : checkPrefixCuts (2^48) 6002966529 10 Manual.Count131072.C045769.packed 64 cuts45769 = true := by
 decide +kernel
def pointBounds45769 : List (Nat × Nat × Nat) := [(6003036160,110554531770775,110554918262176)]
theorem point_links_checked45769 : (cuts45769.take 1).map (fun c => (6002966529-1+2*2^10*c.k,110554386649241+c.lower,110554773140560+c.upper)) = pointBounds45769 := by
 decide +kernel
def cuts45770 : List PrefixCut := [⟨62,266650817,266650965⟩,
⟨64,274527878,274528031⟩]
theorem checked45770 : checkPrefixCuts (2^48) 6003097601 10 Manual.Count131072.C045770.packed 64 cuts45770 = true := by
 decide +kernel
def pointBounds45770 : List (Nat × Nat × Nat) := [(6003224576,110554928959228,110555315450850)]
theorem point_links_checked45770 : (cuts45770.take 1).map (fun c => (6003097601-1+2*2^10*c.k,110554662308411+c.lower,110555048799885+c.upper)) = pointBounds45770 := by
 decide +kernel
def cuts45771 : List PrefixCut := [⟨64,269645618,269645771⟩]
theorem checked45771 : checkPrefixCuts (2^48) 6003228673 10 Manual.Count131072.C045771.packed 64 cuts45771 = true := by
 decide +kernel
def cuts45772 : List PrefixCut := [⟨26,110744781,110744848⟩,
⟨64,273671919,273672079⟩]
theorem checked45772 : checkPrefixCuts (2^48) 6003359745 10 Manual.Count131072.C045772.packed 64 cuts45772 = true := by
 decide +kernel
def pointBounds45772 : List (Nat × Nat × Nat) := [(6003412992,110555317226688,110555703718535)]
theorem point_links_checked45772 : (cuts45772.take 1).map (fun c => (6003359745-1+2*2^10*c.k,110555206481907+c.lower,110555592973687+c.upper)) = pointBounds45772 := by
 decide +kernel
def cuts45773 : List PrefixCut := [⟨54,232970427,232970562⟩,
⟨64,274603650,274603812⟩]
theorem checked45773 : checkPrefixCuts (2^48) 6003490817 10 Manual.Count131072.C045773.packed 64 cuts45773 = true := by
 decide +kernel
def pointBounds45773 : List (Nat × Nat × Nat) := [(6003601408,110555713124253,110556099616328)]
theorem point_links_checked45773 : (cuts45773.take 1).map (fun c => (6003490817-1+2*2^10*c.k,110555480153826+c.lower,110555866645766+c.upper)) = pointBounds45773 := by
 decide +kernel
def cuts45774 : List PrefixCut := [⟨64,269487330,269487487⟩]
theorem checked45774 : checkPrefixCuts (2^48) 6003621889 10 Manual.Count131072.C045774.packed 64 cuts45774 = true := by
 decide +kernel
def cuts45775 : List PrefixCut := [⟨18,76325547,76325590⟩,
⟨64,273700887,273701046⟩]
theorem checked45775 : checkPrefixCuts (2^48) 6003752961 10 Manual.Count131072.C045775.packed 64 cuts45775 = true := by
 decide +kernel
def pointBounds45775 : List (Nat × Nat × Nat) := [(6003789824,110556100570353,110556487062655)]
theorem point_links_checked45775 : (cuts45775.take 1).map (fun c => (6003752961-1+2*2^10*c.k,110556024244806+c.lower,110556410737065+c.upper)) = pointBounds45775 := by
 decide +kernel
def cuts45776 : List PrefixCut := [⟨46,196669011,196669125⟩,
⟨64,272897932,272898089⟩]
theorem checked45776 : checkPrefixCuts (2^48) 6003884033 10 Manual.Count131072.C045776.packed 64 cuts45776 = true := by
 decide +kernel
def pointBounds45776 : List (Nat × Nat × Nat) := [(6003978240,110556494614704,110556881107236)]
theorem point_links_checked45776 : (cuts45776.take 1).map (fun c => (6003884033-1+2*2^10*c.k,110556297945693+c.lower,110556684438111+c.upper)) = pointBounds45776 := by
 decide +kernel
def cuts45777 : List PrefixCut := [⟨64,273407653,273407814⟩]
theorem checked45777 : checkPrefixCuts (2^48) 6004015105 10 Manual.Count131072.C045777.packed 64 cuts45777 = true := by
 decide +kernel
def cuts45778 : List PrefixCut := [⟨10,44911047,44911071⟩,
⟨64,277292724,277292887⟩]
theorem checked45778 : checkPrefixCuts (2^48) 6004146177 10 Manual.Count131072.C045778.packed 64 cuts45778 = true := by
 decide +kernel
def pointBounds45778 : List (Nat × Nat × Nat) := [(6004166656,110556889162325,110557275655085)]
theorem point_links_checked45778 : (cuts45778.take 1).map (fun c => (6004146177-1+2*2^10*c.k,110556844251278+c.lower,110557230744014+c.upper)) = pointBounds45778 := by
 decide +kernel
def cuts45779 : List PrefixCut := [⟨38,164919471,164919568⟩,
⟨64,277239757,277239921⟩]
theorem checked45779 : checkPrefixCuts (2^48) 6004277249 10 Manual.Count131072.C045779.packed 64 cuts45779 = true := by
 decide +kernel
def pointBounds45779 : List (Nat × Nat × Nat) := [(6004355072,110557286463473,110557672956469)]
theorem point_links_checked45779 : (cuts45779.take 1).map (fun c => (6004277249-1+2*2^10*c.k,110557121544002+c.lower,110557508036901+c.upper)) = pointBounds45779 := by
 decide +kernel
def cuts45780 : List PrefixCut := [⟨64,272311572,272311730⟩]
theorem checked45780 : checkPrefixCuts (2^48) 6004408321 10 Manual.Count131072.C045780.packed 64 cuts45780 = true := by
 decide +kernel
def cuts45781 : List PrefixCut := [⟨2,7781582,7781587⟩,
⟨64,274321309,274321472⟩]
theorem checked45781 : checkPrefixCuts (2^48) 6004539393 10 Manual.Count131072.C045781.packed 64 cuts45781 = true := by
 decide +kernel
def pointBounds45781 : List (Nat × Nat × Nat) := [(6004543488,110557678876913,110558065370139)]
theorem point_links_checked45781 : (cuts45781.take 1).map (fun c => (6004539393-1+2*2^10*c.k,110557671095331+c.lower,110558057588552+c.upper)) = pointBounds45781 := by
 decide +kernel
def cuts45782 : List PrefixCut := [⟨30,127830187,127830263⟩,
⟨64,272487184,272487348⟩]
theorem checked45782 : checkPrefixCuts (2^48) 6004670465 10 Manual.Count131072.C045782.packed 64 cuts45782 = true := by
 decide +kernel
def pointBounds45782 : List (Nat × Nat × Nat) := [(6004731904,110558073246827,110558459740287)]
theorem point_links_checked45782 : (cuts45782.take 1).map (fun c => (6004670465-1+2*2^10*c.k,110557945416640+c.lower,110558331910024+c.upper)) = pointBounds45782 := by
 decide +kernel
def cuts45783 : List PrefixCut := [⟨58,247966147,247966291⟩,
⟨64,274168712,274168869⟩]
theorem checked45783 : checkPrefixCuts (2^48) 6004801537 10 Manual.Count131072.C045783.packed 64 cuts45783 = true := by
 decide +kernel
def pointBounds45783 : List (Nat × Nat × Nat) := [(6004920320,110558465869971,110558852363663)]
theorem point_links_checked45783 : (cuts45783.take 1).map (fun c => (6004801537-1+2*2^10*c.k,110558217903824+c.lower,110558604397372+c.upper)) = pointBounds45783 := by
 decide +kernel
def cuts45784 : List PrefixCut := [⟨64,272240944,272241097⟩]
theorem checked45784 : checkPrefixCuts (2^48) 6004932609 10 Manual.Count131072.C045784.packed 64 cuts45784 = true := by
 decide +kernel
def cuts45785 : List PrefixCut := [⟨22,93745499,93745554⟩,
⟨64,270547590,270547747⟩]
theorem checked45785 : checkPrefixCuts (2^48) 6005063681 10 Manual.Count131072.C045785.packed 64 cuts45785 = true := by
 decide +kernel
def pointBounds45785 : List (Nat × Nat × Nat) := [(6005108736,110558858058979,110559244552892)]
theorem point_links_checked45785 : (cuts45785.take 1).map (fun c => (6005063681-1+2*2^10*c.k,110558764313480+c.lower,110559150807338+c.upper)) = pointBounds45785 := by
 decide +kernel
def cuts45786 : List PrefixCut := [⟨50,212702864,212702988⟩,
⟨64,271244728,271244886⟩]
theorem checked45786 : checkPrefixCuts (2^48) 6005194753 10 Manual.Count131072.C045786.packed 64 cuts45786 = true := by
 decide +kernel
def pointBounds45786 : List (Nat × Nat × Nat) := [(6005297152,110559247563934,110559634058073)]
theorem point_links_checked45786 : (cuts45786.take 1).map (fun c => (6005194753-1+2*2^10*c.k,110559034861070+c.lower,110559421355085+c.upper)) = pointBounds45786 := by
 decide +kernel
def cuts45787 : List PrefixCut := [⟨64,272035625,272035779⟩]
theorem checked45787 : checkPrefixCuts (2^48) 6005325825 10 Manual.Count131072.C045787.packed 64 cuts45787 = true := by
 decide +kernel
def cuts45788 : List PrefixCut := [⟨14,59571441,59571475⟩,
⟨64,270482986,270483144⟩]
theorem checked45788 : checkPrefixCuts (2^48) 6005456897 10 Manual.Count131072.C045788.packed 64 cuts45788 = true := by
 decide +kernel
def pointBounds45788 : List (Nat × Nat × Nat) := [(6005485568,110559637712864,110560024207225)]
theorem point_links_checked45788 : (cuts45788.take 1).map (fun c => (6005456897-1+2*2^10*c.k,110559578141423+c.lower,110559964635750+c.upper)) = pointBounds45788 := by
 decide +kernel
def cuts45789 : List PrefixCut := [⟨42,179037672,179037772⟩,
⟨64,275398251,275398403⟩]
theorem checked45789 : checkPrefixCuts (2^48) 6005587969 10 Manual.Count131072.C045789.packed 64 cuts45789 = true := by
 decide +kernel
def pointBounds45789 : List (Nat × Nat × Nat) := [(6005673984,110560027662081,110560414156666)]
theorem point_links_checked45789 : (cuts45789.take 1).map (fun c => (6005587969-1+2*2^10*c.k,110559848624409+c.lower,110560235118894+c.upper)) = pointBounds45789 := by
 decide +kernel
def cuts45790 : List PrefixCut := [⟨64,269908784,269908944⟩]
theorem checked45790 : checkPrefixCuts (2^48) 6005719041 10 Manual.Count131072.C045790.packed 64 cuts45790 = true := by
 decide +kernel
def cuts45791 : List PrefixCut := [⟨6,26151641,26151656⟩,
⟨64,273042922,273043076⟩]
theorem checked45791 : checkPrefixCuts (2^48) 6005850113 10 Manual.Count131072.C045791.packed 64 cuts45791 = true := by
 decide +kernel
def pointBounds45791 : List (Nat × Nat × Nat) := [(6005862400,110560420083085,110560806577897)]
theorem point_links_checked45791 : (cuts45791.take 1).map (fun c => (6005850113-1+2*2^10*c.k,110560393931444+c.lower,110560780426241+c.upper)) = pointBounds45791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000180
