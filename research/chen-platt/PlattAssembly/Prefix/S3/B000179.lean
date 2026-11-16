import PlattAssemblyKernel
import PlattCertificates.Count131072.C025728
import PlattCertificates.Count131072.C025729
import PlattCertificates.Count131072.C025730
import PlattCertificates.Count131072.C025731
import PlattCertificates.Count131072.C025732
import PlattCertificates.Count131072.C025733
import PlattCertificates.Count131072.C025734
import PlattCertificates.Count131072.C025735
import PlattCertificates.Count131072.C025736
import PlattCertificates.Count131072.C025737
import PlattCertificates.Count131072.C025738
import PlattCertificates.Count131072.C025739
import PlattCertificates.Count131072.C025740
import PlattCertificates.Count131072.C025741
import PlattCertificates.Count131072.C025742
import PlattCertificates.Count131072.C025743
import PlattCertificates.Count131072.C025744
import PlattCertificates.Count131072.C025745
import PlattCertificates.Count131072.C025746
import PlattCertificates.Count131072.C025747
import PlattCertificates.Count131072.C025748
import PlattCertificates.Count131072.C025749
import PlattCertificates.Count131072.C025750
import PlattCertificates.Count131072.C025751
import PlattCertificates.Count131072.C025752
import PlattCertificates.Count131072.C025753
import PlattCertificates.Count131072.C025754
import PlattCertificates.Count131072.C025755
import PlattCertificates.Count131072.C025756
import PlattCertificates.Count131072.C025757
import PlattCertificates.Count131072.C025758
import PlattCertificates.Count131072.C025759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25728 : List PrefixCut := [⟨54,210427957,210428071⟩,
⟨128,498301831,498302108⟩]
theorem checked25728 : checkPrefixCuts (2^48) 3376152577 9 Manual.Count131072.C025728.packed 128 cuts25728 = true := by
 decide +kernel
def pointBounds25728 : List (Nat × Nat × Nat) := [(3376207872,103266256552331,103266638775155)]
theorem point_links_checked25728 : (cuts25728.take 1).map (fun c => (3376152577-1+2*2^9*c.k,103266046124374+c.lower,103266428347084+c.upper)) = pointBounds25728 := by
 decide +kernel
def cuts25729 : List PrefixCut := [⟨30,115631257,115631319⟩,
⟨128,495531365,495531642⟩]
theorem checked25729 : checkPrefixCuts (2^48) 3376283649 9 Manual.Count131072.C025729.packed 128 cuts25729 = true := by
 decide +kernel
def pointBounds25729 : List (Nat × Nat × Nat) := [(3376314368,103266660057462,103267042280511)]
theorem point_links_checked25729 : (cuts25729.take 1).map (fun c => (3376283649-1+2*2^9*c.k,103266544426205+c.lower,103266926649192+c.upper)) = pointBounds25729 := by
 decide +kernel
def cuts25730 : List PrefixCut := [⟨6,23342184,23342198⟩,
⟨110,430239796,430240036⟩,
⟨128,499346903,499347186⟩]
theorem checked25730 : checkPrefixCuts (2^48) 3376414721 9 Manual.Count131072.C025730.packed 128 cuts25730 = true := by
 decide +kernel
def pointBounds25730 : List (Nat × Nat × Nat) := [(3376420864,103267063299754,103267445523032),(3376527360,103267470197366,103267852420870)]
theorem point_links_checked25730 : (cuts25730.take 2).map (fun c => (3376414721-1+2*2^9*c.k,103267039957570+c.lower,103267422180834+c.upper)) = pointBounds25730 := by
 decide +kernel
def cuts25731 : List PrefixCut := [⟨86,341612123,341612312⟩,
⟨128,502995292,502995570⟩]
theorem checked25731 : checkPrefixCuts (2^48) 3376545793 9 Manual.Count131072.C025731.packed 128 cuts25731 = true := by
 decide +kernel
def pointBounds25731 : List (Nat × Nat × Nat) := [(3376633856,103267880916596,103268263140332)]
theorem point_links_checked25731 : (cuts25731.take 1).map (fun c => (3376545793-1+2*2^9*c.k,103267539304473+c.lower,103267921528020+c.upper)) = pointBounds25731 := by
 decide +kernel
def cuts25732 : List PrefixCut := [⟨62,234151968,234152099⟩,
⟨128,491972537,491972810⟩]
theorem checked25732 : checkPrefixCuts (2^48) 3376676865 9 Manual.Count131072.C025732.packed 128 cuts25732 = true := by
 decide +kernel
def pointBounds25732 : List (Nat × Nat × Nat) := [(3376740352,103268276451733,103268658675689)]
theorem point_links_checked25732 : (cuts25732.take 1).map (fun c => (3376676865-1+2*2^9*c.k,103268042299765+c.lower,103268424523590+c.upper)) = pointBounds25732 := by
 decide +kernel
def cuts25733 : List PrefixCut := [⟨38,150705545,150705629⟩,
⟨128,508874290,508874572⟩]
theorem checked25733 : checkPrefixCuts (2^48) 3376807937 9 Manual.Count131072.C025733.packed 128 cuts25733 = true := by
 decide +kernel
def pointBounds25733 : List (Nat × Nat × Nat) := [(3376846848,103268684977847,103269067202029)]
theorem point_links_checked25733 : (cuts25733.take 1).map (fun c => (3376807937-1+2*2^9*c.k,103268534272302+c.lower,103268916496400+c.upper)) = pointBounds25733 := by
 decide +kernel
def cuts25734 : List PrefixCut := [⟨14,53261868,53261899⟩,
⟨118,453843949,453844206⟩,
⟨128,492184478,492184757⟩]
theorem checked25734 : checkPrefixCuts (2^48) 3376939009 9 Manual.Count131072.C025734.packed 128 cuts25734 = true := by
 decide +kernel
def pointBounds25734 : List (Nat × Nat × Nat) := [(3376953344,103269096408460,103269478632871),(3377059840,103269496990541,103269879215178)]
theorem point_links_checked25734 : (cuts25734.take 2).map (fun c => (3376939009-1+2*2^9*c.k,103269043146592+c.lower,103269425370972+c.upper)) = pointBounds25734 := by
 decide +kernel
def cuts25735 : List PrefixCut := [⟨94,368813347,368813559⟩,
⟨128,502083660,502083947⟩]
theorem checked25735 : checkPrefixCuts (2^48) 3377070081 9 Manual.Count131072.C025735.packed 128 cuts25735 = true := by
 decide +kernel
def pointBounds25735 : List (Nat × Nat × Nat) := [(3377166336,103269904144417,103270286369288)]
theorem point_links_checked25735 : (cuts25735.take 1).map (fun c => (3377070081-1+2*2^9*c.k,103269535331070+c.lower,103269917555729+c.upper)) = pointBounds25735 := by
 decide +kernel
def cuts25736 : List PrefixCut := [⟨70,270370332,270370482⟩,
⟨128,494063253,494063530⟩]
theorem checked25736 : checkPrefixCuts (2^48) 3377201153 9 Manual.Count131072.C025736.packed 128 cuts25736 = true := by
 decide +kernel
def pointBounds25736 : List (Nat × Nat × Nat) := [(3377272832,103270307785062,103270690010158)]
theorem point_links_checked25736 : (cuts25736.take 1).map (fun c => (3377201153-1+2*2^9*c.k,103270037414730+c.lower,103270419639676+c.upper)) = pointBounds25736 := by
 decide +kernel
def cuts25737 : List PrefixCut := [⟨46,175767863,175767963⟩,
⟨128,498627745,498628023⟩]
theorem checked25737 : checkPrefixCuts (2^48) 3377332225 9 Manual.Count131072.C025737.packed 128 cuts25737 = true := by
 decide +kernel
def pointBounds25737 : List (Nat × Nat × Nat) := [(3377379328,103270707245846,103271089471169)]
theorem point_links_checked25737 : (cuts25737.take 1).map (fun c => (3377332225-1+2*2^9*c.k,103270531477983+c.lower,103270913703206+c.upper)) = pointBounds25737 := by
 decide +kernel
def cuts25738 : List PrefixCut := [⟨22,85088979,85089026⟩,
⟨126,491024851,491025122⟩,
⟨128,498358413,498358689⟩]
theorem checked25738 : checkPrefixCuts (2^48) 3377463297 9 Manual.Count131072.C025738.packed 128 cuts25738 = true := by
 decide +kernel
def pointBounds25738 : List (Nat × Nat × Nat) := [(3377485824,103271115194707,103271497420255),(3377592320,103271521130579,103271903356351)]
theorem point_links_checked25738 : (cuts25738.take 2).map (fun c => (3377463297-1+2*2^9*c.k,103271030105728+c.lower,103271412331229+c.upper)) = pointBounds25738 := by
 decide +kernel
def cuts25739 : List PrefixCut := [⟨102,390756072,390756294⟩,
⟨128,493088997,493089276⟩]
theorem checked25739 : checkPrefixCuts (2^48) 3377594369 9 Manual.Count131072.C025739.packed 128 cuts25739 = true := by
 decide +kernel
def pointBounds25739 : List (Nat × Nat × Nat) := [(3377698816,103271919220213,103272301446212)]
theorem point_links_checked25739 : (cuts25739.take 1).map (fun c => (3377594369-1+2*2^9*c.k,103271528464141+c.lower,103271910689918+c.upper)) = pointBounds25739 := by
 decide +kernel
def cuts25740 : List PrefixCut := [⟨78,299160739,299160905⟩,
⟨128,495569720,495569998⟩]
theorem checked25740 : checkPrefixCuts (2^48) 3377725441 9 Manual.Count131072.C025740.packed 128 cuts25740 = true := by
 decide +kernel
def pointBounds25740 : List (Nat × Nat × Nat) := [(3377805312,103272320713877,103272702940099)]
theorem point_links_checked25740 : (cuts25740.take 1).map (fun c => (3377725441-1+2*2^9*c.k,103272021553138+c.lower,103272403779194+c.upper)) = pointBounds25740 := by
 decide +kernel
def cuts25741 : List PrefixCut := [⟨54,211238404,211238524⟩,
⟨128,498300392,498300676⟩]
theorem checked25741 : checkPrefixCuts (2^48) 3377856513 9 Manual.Count131072.C025741.packed 128 cuts25741 = true := by
 decide +kernel
def pointBounds25741 : List (Nat × Nat × Nat) := [(3377911808,103272728361262,103273110587716)]
theorem point_links_checked25741 : (cuts25741.take 1).map (fun c => (3377856513-1+2*2^9*c.k,103272517122858+c.lower,103272899349192+c.upper)) = pointBounds25741 := by
 decide +kernel
def cuts25742 : List PrefixCut := [⟨30,112156567,112156630⟩,
⟨128,498280964,498281240⟩]
theorem checked25742 : checkPrefixCuts (2^48) 3377987585 9 Manual.Count131072.C025742.packed 128 cuts25742 = true := by
 decide +kernel
def pointBounds25742 : List (Nat × Nat × Nat) := [(3378018304,103273127579817,103273509806498)]
theorem point_links_checked25742 : (cuts25742.take 1).map (fun c => (3377987585-1+2*2^9*c.k,103273015423250+c.lower,103273397649868+c.upper)) = pointBounds25742 := by
 decide +kernel
def cuts25743 : List PrefixCut := [⟨6,22330537,22330549⟩,
⟨110,421273932,421274166⟩,
⟨128,493345708,493345980⟩]
theorem checked25743 : checkPrefixCuts (2^48) 3378118657 9 Manual.Count131072.C025743.packed 128 cuts25743 = true := by
 decide +kernel
def pointBounds25743 : List (Nat × Nat × Nat) := [(3378124800,103273536034751,103273918261657),(3378231296,103273934978146,103274317205274)]
theorem point_links_checked25743 : (cuts25743.take 2).map (fun c => (3378118657-1+2*2^9*c.k,103273513704214+c.lower,103273895931108+c.upper)) = pointBounds25743 := by
 decide +kernel
def cuts25744 : List PrefixCut := [⟨86,338857014,338857198⟩,
⟨128,499992168,499992444⟩]
theorem checked25744 : checkPrefixCuts (2^48) 3378249729 9 Manual.Count131072.C025744.packed 128 cuts25744 = true := by
 decide +kernel
def pointBounds25744 : List (Nat × Nat × Nat) := [(3378337792,103274345906936,103274728134286)]
theorem point_links_checked25744 : (cuts25744.take 1).map (fun c => (3378249729-1+2*2^9*c.k,103274007049922+c.lower,103274389277088+c.upper)) = pointBounds25744 := by
 decide +kernel
def cuts25745 : List PrefixCut := [⟨62,237116589,237116720⟩,
⟨128,491391294,491391572⟩]
theorem checked25745 : checkPrefixCuts (2^48) 3378380801 9 Manual.Count131072.C025745.packed 128 cuts25745 = true := by
 decide +kernel
def pointBounds25745 : List (Nat × Nat × Nat) := [(3378444288,103274744158679,103275126386252)]
theorem point_links_checked25745 : (cuts25745.take 1).map (fun c => (3378380801-1+2*2^9*c.k,103274507042090+c.lower,103274889269532+c.upper)) = pointBounds25745 := by
 decide +kernel
def cuts25746 : List PrefixCut := [⟨38,152795664,152795752⟩,
⟨128,503369085,503369374⟩]
theorem checked25746 : checkPrefixCuts (2^48) 3378511873 9 Manual.Count131072.C025746.packed 128 cuts25746 = true := by
 decide +kernel
def pointBounds25746 : List (Nat × Nat × Nat) := [(3378550784,103275151229048,103275533456856)]
theorem point_links_checked25746 : (cuts25746.take 1).map (fun c => (3378511873-1+2*2^9*c.k,103274998433384+c.lower,103275380661104+c.upper)) = pointBounds25746 := by
 decide +kernel
def cuts25747 : List PrefixCut := [⟨14,54401345,54401376⟩,
⟨118,457114091,457114343⟩,
⟨128,497018115,497018389⟩]
theorem checked25747 : checkPrefixCuts (2^48) 3378642945 9 Manual.Count131072.C025747.packed 128 cuts25747 = true := by
 decide +kernel
def pointBounds25747 : List (Nat × Nat × Nat) := [(3378657280,103275556203814,103275938431854),(3378763776,103275958916560,103276341144821)]
theorem point_links_checked25747 : (cuts25747.take 2).map (fun c => (3378642945-1+2*2^9*c.k,103275501802469+c.lower,103275884030478+c.upper)) = pointBounds25747 := by
 decide +kernel
def cuts25748 : List PrefixCut := [⟨94,360046865,360047070⟩,
⟨128,493499898,493500173⟩]
theorem checked25748 : checkPrefixCuts (2^48) 3378774017 9 Manual.Count131072.C025748.packed 128 cuts25748 = true := by
 decide +kernel
def pointBounds25748 : List (Nat × Nat × Nat) := [(3378870272,103276358867449,103276741095937)]
theorem point_links_checked25748 : (cuts25748.take 1).map (fun c => (3378774017-1+2*2^9*c.k,103275998820584+c.lower,103276381048867+c.upper)) = pointBounds25748 := by
 decide +kernel
def cuts25749 : List PrefixCut := [⟨70,274149168,274149319⟩,
⟨128,500644788,500645066⟩]
theorem checked25749 : checkPrefixCuts (2^48) 3378905089 9 Manual.Count131072.C025749.packed 128 cuts25749 = true := by
 decide +kernel
def pointBounds25749 : List (Nat × Nat × Nat) := [(3378976768,103276766469650,103277148698359)]
theorem point_links_checked25749 : (cuts25749.take 1).map (fun c => (3378905089-1+2*2^9*c.k,103276492320482+c.lower,103276874549040+c.upper)) = pointBounds25749 := by
 decide +kernel
def cuts25750 : List PrefixCut := [⟨46,178678000,178678100⟩,
⟨128,502124733,502125018⟩]
theorem checked25750 : checkPrefixCuts (2^48) 3379036161 9 Manual.Count131072.C025750.packed 128 cuts25750 = true := by
 decide +kernel
def pointBounds25750 : List (Nat × Nat × Nat) := [(3379083264,103277171643270,103277553872206)]
theorem point_links_checked25750 : (cuts25750.take 1).map (fun c => (3379036161-1+2*2^9*c.k,103276992965270+c.lower,103277375194106+c.upper)) = pointBounds25750 := by
 decide +kernel
def cuts25751 : List PrefixCut := [⟨22,86795307,86795355⟩,
⟨126,485029853,485030126⟩,
⟨128,491276896,491277173⟩]
theorem checked25751 : checkPrefixCuts (2^48) 3379167233 9 Manual.Count131072.C025751.packed 128 cuts25751 = true := by
 decide +kernel
def pointBounds25751 : List (Nat × Nat × Nat) := [(3379189760,103277581885310,103277964114479),(3379296256,103277980119856,103278362349250)]
theorem point_links_checked25751 : (cuts25751.take 2).map (fun c => (3379167233-1+2*2^9*c.k,103277495090003+c.lower,103277877319124+c.upper)) = pointBounds25751 := by
 decide +kernel
def cuts25752 : List PrefixCut := [⟨102,396805953,396806177⟩,
⟨128,498420959,498421238⟩]
theorem checked25752 : checkPrefixCuts (2^48) 3379298305 9 Manual.Count131072.C025752.packed 128 cuts25752 = true := by
 decide +kernel
def pointBounds25752 : List (Nat × Nat × Nat) := [(3379402752,103278383172852,103278765402474)]
theorem point_links_checked25752 : (cuts25752.take 1).map (fun c => (3379298305-1+2*2^9*c.k,103277986366899+c.lower,103278368596297+c.upper)) = pointBounds25752 := by
 decide +kernel
def cuts25753 : List PrefixCut := [⟨78,302757991,302758158⟩,
⟨128,501150128,501150403⟩]
theorem checked25753 : checkPrefixCuts (2^48) 3379429377 9 Manual.Count131072.C025753.packed 128 cuts25753 = true := by
 decide +kernel
def pointBounds25753 : List (Nat × Nat × Nat) := [(3379509248,103278787545849,103279169775693)]
theorem point_links_checked25753 : (cuts25753.take 1).map (fun c => (3379429377-1+2*2^9*c.k,103278484787858+c.lower,103278867017535+c.upper)) = pointBounds25753 := by
 decide +kernel
def cuts25754 : List PrefixCut := [⟨54,206717701,206717821⟩,
⟨128,498798668,498798953⟩]
theorem checked25754 : checkPrefixCuts (2^48) 3379560449 9 Manual.Count131072.C025754.packed 128 cuts25754 = true := by
 decide +kernel
def pointBounds25754 : List (Nat × Nat × Nat) := [(3379615744,103279192655687,103279574885759)]
theorem point_links_checked25754 : (cuts25754.take 1).map (fun c => (3379560449-1+2*2^9*c.k,103278985937986+c.lower,103279368167938+c.upper)) = pointBounds25754 := by
 decide +kernel
def cuts25755 : List PrefixCut := [⟨30,117430200,117430266⟩,
⟨128,499112494,499112771⟩]
theorem checked25755 : checkPrefixCuts (2^48) 3379691521 9 Manual.Count131072.C025755.packed 128 cuts25755 = true := by
 decide +kernel
def pointBounds25755 : List (Nat × Nat × Nat) := [(3379722240,103279602166854,103279984397157)]
theorem point_links_checked25755 : (cuts25755.take 1).map (fun c => (3379691521-1+2*2^9*c.k,103279484736654+c.lower,103279866966891+c.upper)) = pointBounds25755 := by
 decide +kernel
def cuts25756 : List PrefixCut := [⟨6,22735682,22735696⟩,
⟨110,421727756,421727996⟩,
⟨128,491597968,491598245⟩]
theorem checked25756 : checkPrefixCuts (2^48) 3379822593 9 Manual.Count131072.C025756.packed 128 cuts25756 = true := by
 decide +kernel
def pointBounds25756 : List (Nat × Nat × Nat) := [(3379828736,103280006584830,103280388815358),(3379935232,103280405576904,103280787807658)]
theorem point_links_checked25756 : (cuts25756.take 2).map (fun c => (3379822593-1+2*2^9*c.k,103279983849148+c.lower,103280366079662+c.upper)) = pointBounds25756 := by
 decide +kernel
def cuts25757 : List PrefixCut := [⟨86,334438993,334439179⟩,
⟨128,498157713,498157989⟩]
theorem checked25757 : checkPrefixCuts (2^48) 3379953665 9 Manual.Count131072.C025757.packed 128 cuts25757 = true := by
 decide +kernel
def pointBounds25757 : List (Nat × Nat × Nat) := [(3380041728,103280809886109,103281192117086)]
theorem point_links_checked25757 : (cuts25757.take 1).map (fun c => (3379953665-1+2*2^9*c.k,103280475447116+c.lower,103280857677907+c.upper)) = pointBounds25757 := by
 decide +kernel
def cuts25758 : List PrefixCut := [⟨62,240078173,240078308⟩,
⟨128,493391962,493392241⟩]
theorem checked25758 : checkPrefixCuts (2^48) 3380084737 9 Manual.Count131072.C025758.packed 128 cuts25758 = true := by
 decide +kernel
def pointBounds25758 : List (Nat × Nat × Nat) := [(3380148224,103281213683002,103281595914204)]
theorem point_links_checked25758 : (cuts25758.take 1).map (fun c => (3380084737-1+2*2^9*c.k,103280973604829+c.lower,103281355835896+c.upper)) = pointBounds25758 := by
 decide +kernel
def cuts25759 : List PrefixCut := [⟨38,148055483,148055566⟩,
⟨128,494288756,494289040⟩]
theorem checked25759 : checkPrefixCuts (2^48) 3380215809 9 Manual.Count131072.C025759.packed 128 cuts25759 = true := by
 decide +kernel
def pointBounds25759 : List (Nat × Nat × Nat) := [(3380254720,103281615052274,103281997283703)]
theorem point_links_checked25759 : (cuts25759.take 1).map (fun c => (3380215809-1+2*2^9*c.k,103281466996791+c.lower,103281849228137+c.upper)) = pointBounds25759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000179
