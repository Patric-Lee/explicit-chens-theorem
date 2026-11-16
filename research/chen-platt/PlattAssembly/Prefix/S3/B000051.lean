import PlattAssemblyKernel
import PlattCertificates.Count131072.C021632
import PlattCertificates.Count131072.C021633
import PlattCertificates.Count131072.C021634
import PlattCertificates.Count131072.C021635
import PlattCertificates.Count131072.C021636
import PlattCertificates.Count131072.C021637
import PlattCertificates.Count131072.C021638
import PlattCertificates.Count131072.C021639
import PlattCertificates.Count131072.C021640
import PlattCertificates.Count131072.C021641
import PlattCertificates.Count131072.C021642
import PlattCertificates.Count131072.C021643
import PlattCertificates.Count131072.C021644
import PlattCertificates.Count131072.C021645
import PlattCertificates.Count131072.C021646
import PlattCertificates.Count131072.C021647
import PlattCertificates.Count131072.C021648
import PlattCertificates.Count131072.C021649
import PlattCertificates.Count131072.C021650
import PlattCertificates.Count131072.C021651
import PlattCertificates.Count131072.C021652
import PlattCertificates.Count131072.C021653
import PlattCertificates.Count131072.C021654
import PlattCertificates.Count131072.C021655
import PlattCertificates.Count131072.C021656
import PlattCertificates.Count131072.C021657
import PlattCertificates.Count131072.C021658
import PlattCertificates.Count131072.C021659
import PlattCertificates.Count131072.C021660
import PlattCertificates.Count131072.C021661
import PlattCertificates.Count131072.C021662
import PlattCertificates.Count131072.C021663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21632 : List PrefixCut := [⟨68,313364934,313365116⟩,
⟨128,592918445,592918783⟩]
theorem checked21632 : checkPrefixCuts (2^48) 2839281665 9 Manual.Count131072.C021632.packed 128 cuts21632 = true := by
 decide +kernel
def pointBounds21632 : List (Nat × Nat × Nat) := [(2839351296,101035818919353,101036199878871)]
theorem point_links_checked21632 : (cuts21632.take 1).map (fun c => (2839281665-1+2*2^9*c.k,101035505554419+c.lower,101035886513755+c.upper)) = pointBounds21632 := by
 decide +kernel
def cuts21633 : List PrefixCut := [⟨27,120642296,120642369⟩,
⟨114,524295086,524295393⟩,
⟨128,592097991,592098335⟩]
theorem checked21633 : checkPrefixCuts (2^48) 2839412737 9 Manual.Count131072.C021633.packed 128 cuts21633 = true := by
 decide +kernel
def pointBounds21633 : List (Nat × Nat × Nat) := [(2839440384,101036219115160,101036600074907),(2839529472,101036622767950,101037003727931)]
theorem point_links_checked21633 : (cuts21633.take 2).map (fun c => (2839412737-1+2*2^9*c.k,101036098472864+c.lower,101036479432538+c.upper)) = pointBounds21633 := by
 decide +kernel
def cuts21634 : List PrefixCut := [⟨73,340198700,340198898⟩,
⟨128,601784846,601785195⟩]
theorem checked21634 : checkPrefixCuts (2^48) 2839543809 9 Manual.Count131072.C021634.packed 128 cuts21634 = true := by
 decide +kernel
def pointBounds21634 : List (Nat × Nat × Nat) := [(2839618560,101037030769555,101037411729771)]
theorem point_links_checked21634 : (cuts21634.take 1).map (fun c => (2839543809-1+2*2^9*c.k,101036690570855+c.lower,101037071530873+c.upper)) = pointBounds21634 := by
 decide +kernel
def cuts21635 : List PrefixCut := [⟨32,152449104,152449191⟩,
⟨119,558244426,558244747⟩,
⟨128,602351852,602352198⟩]
theorem checked21635 : checkPrefixCuts (2^48) 2839674881 9 Manual.Count131072.C021635.packed 128 cuts21635 = true := by
 decide +kernel
def pointBounds21635 : List (Nat × Nat × Nat) := [(2839707648,101037444804805,101037825765259),(2839796736,101037850600127,101038231560815)]
theorem point_links_checked21635 : (cuts21635.take 2).map (fun c => (2839674881-1+2*2^9*c.k,101037292355701+c.lower,101037673316068+c.upper)) = pointBounds21635 := by
 decide +kernel
def cuts21636 : List PrefixCut := [⟨78,362170807,362171015⟩,
⟨128,592908132,592908472⟩]
theorem checked21636 : checkPrefixCuts (2^48) 2839805953 9 Manual.Count131072.C021636.packed 128 cuts21636 = true := by
 decide +kernel
def pointBounds21636 : List (Nat × Nat × Nat) := [(2839885824,101038256878360,101038637839281)]
theorem point_links_checked21636 : (cuts21636.take 1).map (fun c => (2839805953-1+2*2^9*c.k,101037894707553+c.lower,101038275668266+c.upper)) = pointBounds21636 := by
 decide +kernel
def cuts21637 : List PrefixCut := [⟨37,167499986,167500088⟩,
⟨124,570184742,570185079⟩,
⟨128,587826067,587826415⟩]
theorem checked21637 : checkPrefixCuts (2^48) 2839937025 9 Manual.Count131072.C021637.packed 128 cuts21637 = true := by
 decide +kernel
def pointBounds21637 : List (Nat × Nat × Nat) := [(2839974912,101038655115671,101039036076826),(2840064000,101039057800427,101039438761817)]
theorem point_links_checked21637 : (cuts21637.take 2).map (fun c => (2839937025-1+2*2^9*c.k,101038487615685+c.lower,101038868576738+c.upper)) = pointBounds21637 := by
 decide +kernel
def cuts21638 : List PrefixCut := [⟨83,388103072,388103292⟩,
⟨128,597907802,597908143⟩]
theorem checked21638 : checkPrefixCuts (2^48) 2840068097 9 Manual.Count131072.C021638.packed 128 cuts21638 = true := by
 decide +kernel
def pointBounds21638 : List (Nat × Nat × Nat) := [(2840153088,101039463544824,101039844506445)]
theorem point_links_checked21638 : (cuts21638.take 1).map (fun c => (2840068097-1+2*2^9*c.k,101039075441752+c.lower,101039456403153+c.upper)) = pointBounds21638 := by
 decide +kernel
def cuts21639 : List PrefixCut := [⟨42,204053445,204053559⟩,
⟨128,604916490,604916839⟩]
theorem checked21639 : checkPrefixCuts (2^48) 2840199169 9 Manual.Count131072.C021639.packed 128 cuts21639 = true := by
 decide +kernel
def pointBounds21639 : List (Nat × Nat × Nat) := [(2840242176,101039877402999,101040258364855)]
theorem point_links_checked21639 : (cuts21639.take 1).map (fun c => (2840199169-1+2*2^9*c.k,101039673349554+c.lower,101040054311296+c.upper)) = pointBounds21639 := by
 decide +kernel
def cuts21640 : List PrefixCut := [⟨1,4657669,4657672⟩,
⟨88,409967605,409967842⟩,
⟨128,597456295,597456638⟩]
theorem checked21640 : checkPrefixCuts (2^48) 2840330241 9 Manual.Count131072.C021640.packed 128 cuts21640 = true := by
 decide +kernel
def pointBounds21640 : List (Nat × Nat × Nat) := [(2840331264,101040282923713,101040663885807),(2840420352,101040688233649,101041069195977)]
theorem point_links_checked21640 : (cuts21640.take 2).map (fun c => (2840330241-1+2*2^9*c.k,101040278266044+c.lower,101040659228135+c.upper)) = pointBounds21640 := by
 decide +kernel
def cuts21641 : List PrefixCut := [⟨47,214439277,214439398⟩,
⟨128,597824951,597825291⟩]
theorem checked21641 : checkPrefixCuts (2^48) 2840461313 9 Manual.Count131072.C021641.packed 128 cuts21641 = true := by
 decide +kernel
def pointBounds21641 : List (Nat × Nat × Nat) := [(2840509440,101041090161616,101041471124171)]
theorem point_links_checked21641 : (cuts21641.take 1).map (fun c => (2840461313-1+2*2^9*c.k,101040875722339+c.lower,101041256684773+c.upper)) = pointBounds21641 := by
 decide +kernel
def cuts21642 : List PrefixCut := [⟨6,27646139,27646153⟩,
⟨93,427269832,427270074⟩,
⟨128,592545710,592546050⟩]
theorem checked21642 : checkPrefixCuts (2^48) 2840592385 9 Manual.Count131072.C021642.packed 128 cuts21642 = true := by
 decide +kernel
def pointBounds21642 : List (Nat × Nat × Nat) := [(2840598528,101041501193429,101041882156217),(2840687616,101041900817122,101042281780138)]
theorem point_links_checked21642 : (cuts21642.take 2).map (fun c => (2840592385-1+2*2^9*c.k,101041473547290+c.lower,101041854510064+c.upper)) = pointBounds21642 := by
 decide +kernel
def cuts21643 : List PrefixCut := [⟨52,243153886,243154027⟩,
⟨128,598265278,598265619⟩]
theorem checked21643 : checkPrefixCuts (2^48) 2840723457 9 Manual.Count131072.C021643.packed 128 cuts21643 = true := by
 decide +kernel
def pointBounds21643 : List (Nat × Nat × Nat) := [(2840776704,101042309246886,101042690210141)]
theorem point_links_checked21643 : (cuts21643.take 1).map (fun c => (2840723457-1+2*2^9*c.k,101042066093000+c.lower,101042447056114+c.upper)) = pointBounds21643 := by
 decide +kernel
def cuts21644 : List PrefixCut := [⟨11,53701832,53701863⟩,
⟨98,463096726,463096991⟩,
⟨128,604083355,604083699⟩]
theorem checked21644 : checkPrefixCuts (2^48) 2840854529 9 Manual.Count131072.C021644.packed 128 cuts21644 = true := by
 decide +kernel
def pointBounds21644 : List (Nat × Nat × Nat) := [(2840865792,101042718060110,101043099023596),(2840954880,101043127455004,101043508418724)]
theorem point_links_checked21644 : (cuts21644.take 2).map (fun c => (2840854529-1+2*2^9*c.k,101042664358278+c.lower,101043045321733+c.upper)) = pointBounds21644 := by
 decide +kernel
def cuts21645 : List PrefixCut := [⟨57,267206560,267206713⟩,
⟨128,591869404,591869745⟩]
theorem checked21645 : checkPrefixCuts (2^48) 2840985601 9 Manual.Count131072.C021645.packed 128 cuts21645 = true := by
 decide +kernel
def pointBounds21645 : List (Nat × Nat × Nat) := [(2841043968,101043535648193,101043916612145)]
theorem point_links_checked21645 : (cuts21645.take 1).map (fun c => (2840985601-1+2*2^9*c.k,101043268441633+c.lower,101043649405432+c.upper)) = pointBounds21645 := by
 decide +kernel
def cuts21646 : List PrefixCut := [⟨16,74997232,74997276⟩,
⟨103,472861550,472861827⟩,
⟨128,590653171,590653515⟩]
theorem checked21646 : checkPrefixCuts (2^48) 2841116673 9 Manual.Count131072.C021646.packed 128 cuts21646 = true := by
 decide +kernel
def pointBounds21646 : List (Nat × Nat × Nat) := [(2841133056,101043935308269,101044316272453),(2841222144,101044333172587,101044714137004)]
theorem point_links_checked21646 : (cuts21646.take 2).map (fun c => (2841116673-1+2*2^9*c.k,101043860311037+c.lower,101044241275177+c.upper)) = pointBounds21646 := by
 decide +kernel
def cuts21647 : List PrefixCut := [⟨62,287787443,287787612⟩,
⟨128,593102569,593102913⟩]
theorem checked21647 : checkPrefixCuts (2^48) 2841247745 9 Manual.Count131072.C021647.packed 128 cuts21647 = true := by
 decide +kernel
def pointBounds21647 : List (Nat × Nat × Nat) := [(2841311232,101044738751651,101045119716304)]
theorem point_links_checked21647 : (cuts21647.take 1).map (fun c => (2841247745-1+2*2^9*c.k,101044450964208+c.lower,101044831928692+c.upper)) = pointBounds21647 := by
 decide +kernel
def cuts21648 : List PrefixCut := [⟨21,99656784,99656844⟩,
⟨108,502634856,502635144⟩,
⟨128,593372508,593372848⟩]
theorem checked21648 : checkPrefixCuts (2^48) 2841378817 9 Manual.Count131072.C021648.packed 128 cuts21648 = true := by
 decide +kernel
def pointBounds21648 : List (Nat × Nat × Nat) := [(2841400320,101045143723561,101045524688449),(2841489408,101045546701633,101045927666749)]
theorem point_links_checked21648 : (cuts21648.take 2).map (fun c => (2841378817-1+2*2^9*c.k,101045044066777+c.lower,101045425031605+c.upper)) = pointBounds21648 := by
 decide +kernel
def cuts21649 : List PrefixCut := [⟨67,311038997,311039182⟩,
⟨128,589878091,589878438⟩]
theorem checked21649 : checkPrefixCuts (2^48) 2841509889 9 Manual.Count131072.C021649.packed 128 cuts21649 = true := by
 decide +kernel
def pointBounds21649 : List (Nat × Nat × Nat) := [(2841578496,101045948478282,101046329443635)]
theorem point_links_checked21649 : (cuts21649.take 1).map (fun c => (2841509889-1+2*2^9*c.k,101045637439285+c.lower,101046018404453+c.upper)) = pointBounds21649 := by
 decide +kernel
def cuts21650 : List PrefixCut := [⟨26,122330678,122330749⟩,
⟨113,524973675,524973977⟩,
⟨128,597279694,597280039⟩]
theorem checked21650 : checkPrefixCuts (2^48) 2841640961 9 Manual.Count131072.C021650.packed 128 cuts21650 = true := by
 decide +kernel
def pointBounds21650 : List (Nat × Nat × Nat) := [(2841667584,101046349648054,101046730613640),(2841756672,101046752291051,101047133256868)]
theorem point_links_checked21650 : (cuts21650.take 2).map (fun c => (2841640961-1+2*2^9*c.k,101046227317376+c.lower,101046608282891+c.upper)) = pointBounds21650 := by
 decide +kernel
def cuts21651 : List PrefixCut := [⟨72,334781509,334781701⟩,
⟨128,596855903,596856247⟩]
theorem checked21651 : checkPrefixCuts (2^48) 2841772033 9 Manual.Count131072.C021651.packed 128 cuts21651 = true := by
 decide +kernel
def pointBounds21651 : List (Nat × Nat × Nat) := [(2841845760,101047159378579,101047540344631)]
theorem point_links_checked21651 : (cuts21651.take 1).map (fun c => (2841772033-1+2*2^9*c.k,101046824597070+c.lower,101047205562930+c.upper)) = pointBounds21651 := by
 decide +kernel
def cuts21652 : List PrefixCut := [⟨31,145495565,145495648⟩,
⟨118,550873948,550874262⟩,
⟨128,600394008,600394349⟩]
theorem checked21652 : checkPrefixCuts (2^48) 2841903105 9 Manual.Count131072.C021652.packed 128 cuts21652 = true := by
 decide +kernel
def pointBounds21652 : List (Nat × Nat × Nat) := [(2841934848,101047566948538,101047947914825),(2842023936,101047972326921,101048353293439)]
theorem point_links_checked21652 : (cuts21652.take 2).map (fun c => (2841903105-1+2*2^9*c.k,101047421452973+c.lower,101047802419177+c.upper)) = pointBounds21652 := by
 decide +kernel
def cuts21653 : List PrefixCut := [⟨77,359906153,359906349⟩,
⟨128,597395174,597395510⟩]
theorem checked21653 : checkPrefixCuts (2^48) 2842034177 9 Manual.Count131072.C021653.packed 128 cuts21653 = true := by
 decide +kernel
def pointBounds21653 : List (Nat × Nat × Nat) := [(2842113024,101048381753134,101048762719875)]
theorem point_links_checked21653 : (cuts21653.take 1).map (fun c => (2842034177-1+2*2^9*c.k,101048021846981+c.lower,101048402813526+c.upper)) = pointBounds21653 := by
 decide +kernel
def cuts21654 : List PrefixCut := [⟨36,173409809,173409905⟩,
⟨123,573798384,573798709⟩,
⟨128,596476458,596476796⟩]
theorem checked21654 : checkPrefixCuts (2^48) 2842165249 9 Manual.Count131072.C021654.packed 128 cuts21654 = true := by
 decide +kernel
def pointBounds21654 : List (Nat × Nat × Nat) := [(2842202112,101048792651964,101049173618941),(2842291200,101049193040539,101049574007745)]
theorem point_links_checked21654 : (cuts21654.take 2).map (fun c => (2842165249-1+2*2^9*c.k,101048619242155+c.lower,101049000209036+c.upper)) = pointBounds21654 := by
 decide +kernel
def cuts21655 : List PrefixCut := [⟨82,385026038,385026258⟩,
⟨128,597240999,597241345⟩]
theorem checked21655 : checkPrefixCuts (2^48) 2842296321 9 Manual.Count131072.C021655.packed 128 cuts21655 = true := by
 decide +kernel
def pointBounds21655 : List (Nat × Nat × Nat) := [(2842380288,101049600744651,101049981712090)]
theorem point_links_checked21655 : (cuts21655.take 1).map (fun c => (2842296321-1+2*2^9*c.k,101049215718613+c.lower,101049596685832+c.upper)) = pointBounds21655 := by
 decide +kernel
def cuts21656 : List PrefixCut := [⟨41,190921187,190921299⟩,
⟨128,596025192,596025540⟩]
theorem checked21656 : checkPrefixCuts (2^48) 2842427393 9 Manual.Count131072.C021656.packed 128 cuts21656 = true := by
 decide +kernel
def pointBounds21656 : List (Nat × Nat × Nat) := [(2842469376,101050003880799,101050384848476),(2842558464,101050408984804,101050789952717)]
theorem point_links_checked21656 : (cuts21656.take 2).map (fun c => (2842427393-1+2*2^9*c.k,101049812959612+c.lower,101050193927177+c.upper)) = pointBounds21656 := by
 decide +kernel
def cuts21657 : List PrefixCut := [⟨87,406477512,406477743⟩,
⟨128,595403557,595403896⟩]
theorem checked21657 : checkPrefixCuts (2^48) 2842558465 9 Manual.Count131072.C021657.packed 128 cuts21657 = true := by
 decide +kernel
def pointBounds21657 : List (Nat × Nat × Nat) := [(2842647552,101050815462316,101051196430460)]
theorem point_links_checked21657 : (cuts21657.take 1).map (fun c => (2842558465-1+2*2^9*c.k,101050408984804+c.lower,101050789952717+c.upper)) = pointBounds21657 := by
 decide +kernel
def cuts21658 : List PrefixCut := [⟨46,213281066,213281191⟩,
⟨128,593494822,593495163⟩]
theorem checked21658 : checkPrefixCuts (2^48) 2842689537 9 Manual.Count131072.C021658.packed 128 cuts21658 = true := by
 decide +kernel
def pointBounds21658 : List (Nat × Nat × Nat) := [(2842736640,101051217669427,101051598637804)]
theorem point_links_checked21658 : (cuts21658.take 1).map (fun c => (2842689537-1+2*2^9*c.k,101051004388361+c.lower,101051385356613+c.upper)) = pointBounds21658 := by
 decide +kernel
def cuts21659 : List PrefixCut := [⟨5,24357066,24357078⟩,
⟨92,429608363,429608611⟩,
⟨128,597328983,597329328⟩]
theorem checked21659 : checkPrefixCuts (2^48) 2842820609 9 Manual.Count131072.C021659.packed 128 cuts21659 = true := by
 decide +kernel
def pointBounds21659 : List (Nat × Nat × Nat) := [(2842825728,101051622240249,101052003208854),(2842914816,101052027491546,101052408460387)]
theorem point_links_checked21659 : (cuts21659.take 2).map (fun c => (2842820609-1+2*2^9*c.k,101051597883183+c.lower,101051978851776+c.upper)) = pointBounds21659 := by
 decide +kernel
def cuts21660 : List PrefixCut := [⟨51,236131846,236131985⟩,
⟨128,599380381,599380726⟩]
theorem checked21660 : checkPrefixCuts (2^48) 2842951681 9 Manual.Count131072.C021660.packed 128 cuts21660 = true := by
 decide +kernel
def pointBounds21660 : List (Nat × Nat × Nat) := [(2843003904,101052431344012,101052812313089)]
theorem point_links_checked21660 : (cuts21660.take 1).map (fun c => (2842951681-1+2*2^9*c.k,101052195212166+c.lower,101052576181104+c.upper)) = pointBounds21660 := by
 decide +kernel
def cuts21661 : List PrefixCut := [⟨10,45838501,45838525⟩,
⟨97,448873582,448873838⟩,
⟨128,596877689,596878029⟩]
theorem checked21661 : checkPrefixCuts (2^48) 2843082753 9 Manual.Count131072.C021661.packed 128 cuts21661 = true := by
 decide +kernel
def pointBounds21661 : List (Nat × Nat × Nat) := [(2843092992,101052840431048,101053221400355),(2843182080,101053243466129,101053624435668)]
theorem point_links_checked21661 : (cuts21661.take 2).map (fun c => (2843082753-1+2*2^9*c.k,101052794592547+c.lower,101053175561830+c.upper)) = pointBounds21661 := by
 decide +kernel
def cuts21662 : List PrefixCut := [⟨56,253038514,253038661⟩,
⟨128,587049557,587049898⟩]
theorem checked21662 : checkPrefixCuts (2^48) 2843213825 9 Manual.Count131072.C021662.packed 128 cuts21662 = true := by
 decide +kernel
def pointBounds21662 : List (Nat × Nat × Nat) := [(2843271168,101053644508750,101054025478520)]
theorem point_links_checked21662 : (cuts21662.take 1).map (fun c => (2843213825-1+2*2^9*c.k,101053391470236+c.lower,101053772439859+c.upper)) = pointBounds21662 := by
 decide +kernel
def cuts21663 : List PrefixCut := [⟨15,70087765,70087804⟩,
⟨102,477044660,477044937⟩,
⟨128,599198548,599198894⟩]
theorem checked21663 : checkPrefixCuts (2^48) 2843344897 9 Manual.Count131072.C021663.packed 128 cuts21663 = true := by
 decide +kernel
def pointBounds21663 : List (Nat × Nat × Nat) := [(2843360256,101054048607558,101054429577561),(2843449344,101054455564453,101054836534694)]
theorem point_links_checked21663 : (cuts21663.take 2).map (fun c => (2843344897-1+2*2^9*c.k,101053978519793+c.lower,101054359489757+c.upper)) = pointBounds21663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000051
