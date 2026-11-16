import PlattAssemblyKernel
import PlattCertificates.Count131072.C027808
import PlattCertificates.Count131072.C027809
import PlattCertificates.Count131072.C027810
import PlattCertificates.Count131072.C027811
import PlattCertificates.Count131072.C027812
import PlattCertificates.Count131072.C027813
import PlattCertificates.Count131072.C027814
import PlattCertificates.Count131072.C027815
import PlattCertificates.Count131072.C027816
import PlattCertificates.Count131072.C027817
import PlattCertificates.Count131072.C027818
import PlattCertificates.Count131072.C027819
import PlattCertificates.Count131072.C027820
import PlattCertificates.Count131072.C027821
import PlattCertificates.Count131072.C027822
import PlattCertificates.Count131072.C027823
import PlattCertificates.Count131072.C027824
import PlattCertificates.Count131072.C027825
import PlattCertificates.Count131072.C027826
import PlattCertificates.Count131072.C027827
import PlattCertificates.Count131072.C027828
import PlattCertificates.Count131072.C027829
import PlattCertificates.Count131072.C027830
import PlattCertificates.Count131072.C027831
import PlattCertificates.Count131072.C027832
import PlattCertificates.Count131072.C027833
import PlattCertificates.Count131072.C027834
import PlattCertificates.Count131072.C027835
import PlattCertificates.Count131072.C027836
import PlattCertificates.Count131072.C027837
import PlattCertificates.Count131072.C027838
import PlattCertificates.Count131072.C027839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27808 : List PrefixCut := [⟨28,100052967,100053025⟩,
⟨128,461533154,461533416⟩]
theorem checked27808 : checkPrefixCuts (2^48) 3648782337 9 Manual.Count131072.C027808.packed 128 cuts27808 = true := by
 decide +kernel
def pointBounds27808 : List (Nat × Nat × Nat) := [(3648811008,104260799429401,104261182208745)]
theorem point_links_checked27808 : (cuts27808.take 1).map (fun c => (3648782337-1+2*2^9*c.k,104260699376434+c.lower,104261082155720+c.upper)) = pointBounds27808 := by
 decide +kernel
def cuts27809 : List PrefixCut := [⟨12,43120841,43120864⟩,
⟨124,438838265,438838512⟩,
⟨128,453339954,453340210⟩]
theorem checked27809 : checkPrefixCuts (2^48) 3648913409 9 Manual.Count131072.C027809.packed 128 cuts27809 = true := by
 decide +kernel
def pointBounds27809 : List (Nat × Nat × Nat) := [(3648925696,104261204030429,104261586810000),(3649040384,104261599747853,104261982527648)]
theorem point_links_checked27809 : (cuts27809.take 2).map (fun c => (3648913409-1+2*2^9*c.k,104261160909588+c.lower,104261543689136+c.upper)) = pointBounds27809 := by
 decide +kernel
def cuts27810 : List PrefixCut := [⟨108,387914084,387914295⟩,
⟨128,461114297,461114547⟩]
theorem checked27810 : checkPrefixCuts (2^48) 3649044481 9 Manual.Count131072.C027810.packed 128 cuts27810 = true := by
 decide +kernel
def pointBounds27810 : List (Nat × Nat × Nat) := [(3649155072,104262002163626,104262384943641)]
theorem point_links_checked27810 : (cuts27810.take 1).map (fun c => (3649044481-1+2*2^9*c.k,104261614249542+c.lower,104261997029346+c.upper)) = pointBounds27810 := by
 decide +kernel
def cuts27811 : List PrefixCut := [⟨92,335065020,335065204⟩,
⟨128,467808254,467808511⟩]
theorem checked27811 : checkPrefixCuts (2^48) 3649175553 9 Manual.Count131072.C027811.packed 128 cuts27811 = true := by
 decide +kernel
def pointBounds27811 : List (Nat × Nat × Nat) := [(3649269760,104262410428859,104262793209097)]
theorem point_links_checked27811 : (cuts27811.take 1).map (fun c => (3649175553-1+2*2^9*c.k,104262075363839+c.lower,104262458143893+c.upper)) = pointBounds27811 := by
 decide +kernel
def cuts27812 : List PrefixCut := [⟨76,270187234,270187382⟩,
⟨128,456376293,456376543⟩]
theorem checked27812 : checkPrefixCuts (2^48) 3649306625 9 Manual.Count131072.C027812.packed 128 cuts27812 = true := by
 decide +kernel
def pointBounds27812 : List (Nat × Nat × Nat) := [(3649384448,104262813359327,104263196139786)]
theorem point_links_checked27812 : (cuts27812.take 1).map (fun c => (3649306625-1+2*2^9*c.k,104262543172093+c.lower,104262925952404+c.upper)) = pointBounds27812 := by
 decide +kernel
def cuts27813 : List PrefixCut := [⟨60,219505280,219505402⟩,
⟨128,463764125,463764383⟩]
theorem checked27813 : checkPrefixCuts (2^48) 3649437697 9 Manual.Count131072.C027813.packed 128 cuts27813 = true := by
 decide +kernel
def pointBounds27813 : List (Nat × Nat × Nat) := [(3649499136,104263219053666,104263601834349)]
theorem point_links_checked27813 : (cuts27813.take 1).map (fun c => (3649437697-1+2*2^9*c.k,104262999548386+c.lower,104263382328947+c.upper)) = pointBounds27813 := by
 decide +kernel
def cuts27814 : List PrefixCut := [⟨44,155869722,155869807⟩,
⟨128,461433667,461433921⟩]
theorem checked27814 : checkPrefixCuts (2^48) 3649568769 9 Manual.Count131072.C027814.packed 128 cuts27814 = true := by
 decide +kernel
def pointBounds27814 : List (Nat × Nat × Nat) := [(3649613824,104263619182233,104264001963137)]
theorem point_links_checked27814 : (cuts27814.take 1).map (fun c => (3649568769-1+2*2^9*c.k,104263463312511+c.lower,104263846093330+c.upper)) = pointBounds27814 := by
 decide +kernel
def cuts27815 : List PrefixCut := [⟨28,99025227,99025284⟩,
⟨128,456404253,456404513⟩]
theorem checked27815 : checkPrefixCuts (2^48) 3649699841 9 Manual.Count131072.C027815.packed 128 cuts27815 = true := by
 decide +kernel
def pointBounds27815 : List (Nat × Nat × Nat) := [(3649728512,104264023771405,104264406552535)]
theorem point_links_checked27815 : (cuts27815.take 1).map (fun c => (3649699841-1+2*2^9*c.k,104263924746178+c.lower,104264307527251+c.upper)) = pointBounds27815 := by
 decide +kernel
def cuts27816 : List PrefixCut := [⟨12,43109999,43110025⟩,
⟨124,438805127,438805375⟩,
⟨128,453842992,453843249⟩]
theorem checked27816 : checkPrefixCuts (2^48) 3649830913 9 Manual.Count131072.C027816.packed 128 cuts27816 = true := by
 decide +kernel
def pointBounds27816 : List (Nat × Nat × Nat) := [(3649843200,104264424260430,104264807041789),(3649957888,104264819955558,104265202737139)]
theorem point_links_checked27816 : (cuts27816.take 2).map (fun c => (3649830913-1+2*2^9*c.k,104264381150431+c.lower,104264763931764+c.upper)) = pointBounds27816 := by
 decide +kernel
def cuts27817 : List PrefixCut := [⟨108,385580215,385580431⟩,
⟨128,456911282,456911537⟩]
theorem checked27817 : checkPrefixCuts (2^48) 3649961985 9 Manual.Count131072.C027817.packed 128 cuts27817 = true := by
 decide +kernel
def pointBounds27817 : List (Nat × Nat × Nat) := [(3650072576,104265220573638,104265603355444)]
theorem point_links_checked27817 : (cuts27817.take 1).map (fun c => (3649961985-1+2*2^9*c.k,104264834993423+c.lower,104265217775013+c.upper)) = pointBounds27817 := by
 decide +kernel
def cuts27818 : List PrefixCut := [⟨92,330585332,330585521⟩,
⟨128,461136063,461136326⟩]
theorem checked27818 : checkPrefixCuts (2^48) 3650093057 9 Manual.Count131072.C027818.packed 128 cuts27818 = true := by
 decide +kernel
def pointBounds27818 : List (Nat × Nat × Nat) := [(3650187264,104265622490037,104266005272071)]
theorem point_links_checked27818 : (cuts27818.take 1).map (fun c => (3650093057-1+2*2^9*c.k,104265291904705+c.lower,104265674686550+c.upper)) = pointBounds27818 := by
 decide +kernel
def cuts27819 : List PrefixCut := [⟨76,273589278,273589429⟩,
⟨128,464589433,464589690⟩]
theorem checked27819 : checkPrefixCuts (2^48) 3650224129 9 Manual.Count131072.C027819.packed 128 cuts27819 = true := by
 decide +kernel
def pointBounds27819 : List (Nat × Nat × Nat) := [(3650301952,104266026630046,104266409412305)]
theorem point_links_checked27819 : (cuts27819.take 1).map (fun c => (3650224129-1+2*2^9*c.k,104265753040768+c.lower,104266135822876+c.upper)) = pointBounds27819 := by
 decide +kernel
def cuts27820 : List PrefixCut := [⟨60,212510345,212510466⟩,
⟨128,455088548,455088805⟩]
theorem checked27820 : checkPrefixCuts (2^48) 3650355201 9 Manual.Count131072.C027820.packed 128 cuts27820 = true := by
 decide +kernel
def pointBounds27820 : List (Nat × Nat × Nat) := [(3650416640,104266430140546,104266812923032)]
theorem point_links_checked27820 : (cuts27820.take 1).map (fun c => (3650355201-1+2*2^9*c.k,104266217630201+c.lower,104266600412566+c.upper)) = pointBounds27820 := by
 decide +kernel
def cuts27821 : List PrefixCut := [⟨44,157295536,157295625⟩,
⟨128,462782688,462782951⟩]
theorem checked27821 : checkPrefixCuts (2^48) 3650486273 9 Manual.Count131072.C027821.packed 128 cuts27821 = true := by
 decide +kernel
def pointBounds27821 : List (Nat × Nat × Nat) := [(3650531328,104266830014285,104267212796996)]
theorem point_links_checked27821 : (cuts27821.take 1).map (fun c => (3650486273-1+2*2^9*c.k,104266672718749+c.lower,104267055501371+c.upper)) = pointBounds27821 := by
 decide +kernel
def cuts27822 : List PrefixCut := [⟨28,102392878,102392933⟩,
⟨128,455595695,455595948⟩]
theorem checked27822 : checkPrefixCuts (2^48) 3650617345 9 Manual.Count131072.C027822.packed 128 cuts27822 = true := by
 decide +kernel
def pointBounds27822 : List (Nat × Nat × Nat) := [(3650646016,104267237894315,104267620677255)]
theorem point_links_checked27822 : (cuts27822.take 1).map (fun c => (3650617345-1+2*2^9*c.k,104267135501437+c.lower,104267518284322+c.upper)) = pointBounds27822 := by
 decide +kernel
def cuts27823 : List PrefixCut := [⟨12,42173956,42173982⟩,
⟨124,441547466,441547713⟩,
⟨128,455656378,455656633⟩]
theorem checked27823 : checkPrefixCuts (2^48) 3650748417 9 Manual.Count131072.C027823.packed 128 cuts27823 = true := by
 decide +kernel
def pointBounds27823 : List (Nat × Nat × Nat) := [(3650760704,104267633271088,104268016054252),(3650875392,104268032644598,104268415427983)]
theorem point_links_checked27823 : (cuts27823.take 2).map (fun c => (3650748417-1+2*2^9*c.k,104267591097132+c.lower,104267973880270+c.upper)) = pointBounds27823 := by
 decide +kernel
def cuts27824 : List PrefixCut := [⟨108,392421958,392422179⟩,
⟨128,462964139,462964400⟩]
theorem checked27824 : checkPrefixCuts (2^48) 3650879489 9 Manual.Count131072.C027824.packed 128 cuts27824 = true := by
 decide +kernel
def pointBounds27824 : List (Nat × Nat × Nat) := [(3650990080,104268439175468,104268821959082)]
theorem point_links_checked27824 : (cuts27824.take 1).map (fun c => (3650879489-1+2*2^9*c.k,104268046753510+c.lower,104268429536903+c.upper)) = pointBounds27824 := by
 decide +kernel
def cuts27825 : List PrefixCut := [⟨92,328420731,328420912⟩,
⟨128,458861553,458861806⟩]
theorem checked27825 : checkPrefixCuts (2^48) 3651010561 9 Manual.Count131072.C027825.packed 128 cuts27825 = true := by
 decide +kernel
def pointBounds27825 : List (Nat × Nat × Nat) := [(3651104768,104268838138380,104269220922215)]
theorem point_links_checked27825 : (cuts27825.take 1).map (fun c => (3651010561-1+2*2^9*c.k,104268509717649+c.lower,104268892501303+c.upper)) = pointBounds27825 := by
 decide +kernel
def cuts27826 : List PrefixCut := [⟨76,278068966,278069116⟩,
⟨128,460155767,460156019⟩]
theorem checked27826 : checkPrefixCuts (2^48) 3651141633 9 Manual.Count131072.C027826.packed 128 cuts27826 = true := by
 decide +kernel
def pointBounds27826 : List (Nat × Nat × Nat) := [(3651219456,104269246648168,104269629432225)]
theorem point_links_checked27826 : (cuts27826.take 1).map (fun c => (3651141633-1+2*2^9*c.k,104268968579202+c.lower,104269351363109+c.upper)) = pointBounds27826 := by
 decide +kernel
def cuts27827 : List PrefixCut := [⟨60,215694689,215694813⟩,
⟨128,461835082,461835346⟩]
theorem checked27827 : checkPrefixCuts (2^48) 3651272705 9 Manual.Count131072.C027827.packed 128 cuts27827 = true := by
 decide +kernel
def pointBounds27827 : List (Nat × Nat × Nat) := [(3651334144,104269644429658,104270027213941)]
theorem point_links_checked27827 : (cuts27827.take 1).map (fun c => (3651272705-1+2*2^9*c.k,104269428734969+c.lower,104269811519128+c.upper)) = pointBounds27827 := by
 decide +kernel
def cuts27828 : List PrefixCut := [⟨44,156176816,156176906⟩,
⟨128,460508032,460508290⟩]
theorem checked27828 : checkPrefixCuts (2^48) 3651403777 9 Manual.Count131072.C027828.packed 128 cuts27828 = true := by
 decide +kernel
def pointBounds27828 : List (Nat × Nat × Nat) := [(3651448832,104270046746867,104270429531380)]
theorem point_links_checked27828 : (cuts27828.take 1).map (fun c => (3651403777-1+2*2^9*c.k,104269890570051+c.lower,104270273354474+c.upper)) = pointBounds27828 := by
 decide +kernel
def cuts27829 : List PrefixCut := [⟨28,98050452,98050504⟩,
⟨128,454787333,454787584⟩]
theorem checked27829 : checkPrefixCuts (2^48) 3651534849 9 Manual.Count131072.C027829.packed 128 cuts27829 = true := by
 decide +kernel
def pointBounds27829 : List (Nat × Nat × Nat) := [(3651563520,104270449128535,104270831913268)]
theorem point_links_checked27829 : (cuts27829.take 1).map (fun c => (3651534849-1+2*2^9*c.k,104270351078083+c.lower,104270733862764+c.upper)) = pointBounds27829 := by
 decide +kernel
def cuts27830 : List PrefixCut := [⟨12,43165415,43165439⟩,
⟨124,442515650,442515899⟩,
⟨128,457545959,457546216⟩]
theorem checked27830 : checkPrefixCuts (2^48) 3651665921 9 Manual.Count131072.C027830.packed 128 cuts27830 = true := by
 decide +kernel
def pointBounds27830 : List (Nat × Nat × Nat) := [(3651678208,104270849030831,104271231815787),(3651792896,104271248381066,104271631166247)]
theorem point_links_checked27830 : (cuts27830.take 2).map (fun c => (3651665921-1+2*2^9*c.k,104270805865416+c.lower,104271188650348+c.upper)) = pointBounds27830 := by
 decide +kernel
def cuts27831 : List PrefixCut := [⟨108,385926042,385926261⟩,
⟨128,459148155,459148415⟩]
theorem checked27831 : checkPrefixCuts (2^48) 3651796993 9 Manual.Count131072.C027831.packed 128 cuts27831 = true := by
 decide +kernel
def pointBounds27831 : List (Nat × Nat × Nat) := [(3651907584,104271649337417,104272032122825)]
theorem point_links_checked27831 : (cuts27831.take 1).map (fun c => (3651796993-1+2*2^9*c.k,104271263411375+c.lower,104271646196564+c.upper)) = pointBounds27831 := by
 decide +kernel
def cuts27832 : List PrefixCut := [⟨92,328492399,328492584⟩,
⟨128,456588248,456588505⟩]
theorem checked27832 : checkPrefixCuts (2^48) 3651928065 9 Manual.Count131072.C027832.packed 128 cuts27832 = true := by
 decide +kernel
def pointBounds27832 : List (Nat × Nat × Nat) := [(3652022272,104272051051929,104272433837563)]
theorem point_links_checked27832 : (cuts27832.take 1).map (fun c => (3651928065-1+2*2^9*c.k,104271722559530+c.lower,104272105344979+c.upper)) = pointBounds27832 := by
 decide +kernel
def cuts27833 : List PrefixCut := [⟨76,272449901,272450055⟩,
⟨128,456263596,456263854⟩]
theorem checked27833 : checkPrefixCuts (2^48) 3652059137 9 Manual.Count131072.C027833.packed 128 cuts27833 = true := by
 decide +kernel
def pointBounds27833 : List (Nat × Nat × Nat) := [(3652136960,104272451597679,104272834383539)]
theorem point_links_checked27833 : (cuts27833.take 1).map (fun c => (3652059137-1+2*2^9*c.k,104272179147778+c.lower,104272561933484+c.upper)) = pointBounds27833 := by
 decide +kernel
def cuts27834 : List PrefixCut := [⟨60,219185713,219185836⟩,
⟨128,468192851,468193111⟩]
theorem checked27834 : checkPrefixCuts (2^48) 3652190209 9 Manual.Count131072.C027834.packed 128 cuts27834 = true := by
 decide +kernel
def pointBounds27834 : List (Nat × Nat × Nat) := [(3652251648,104272854597087,104273237383174)]
theorem point_links_checked27834 : (cuts27834.take 1).map (fun c => (3652190209-1+2*2^9*c.k,104272635411374+c.lower,104273018197338+c.upper)) = pointBounds27834 := by
 decide +kernel
def cuts27835 : List PrefixCut := [⟨44,158603734,158603821⟩,
⟨128,458928130,458928385⟩]
theorem checked27835 : checkPrefixCuts (2^48) 3652321281 9 Manual.Count131072.C027835.packed 128 cuts27835 = true := by
 decide +kernel
def pointBounds27835 : List (Nat × Nat × Nat) := [(3652366336,104273262207959,104273644994270)]
theorem point_links_checked27835 : (cuts27835.take 1).map (fun c => (3652321281-1+2*2^9*c.k,104273103604225+c.lower,104273486390449+c.upper)) = pointBounds27835 := by
 decide +kernel
def cuts27836 : List PrefixCut := [⟨28,100800144,100800201⟩,
⟨128,454133713,454133965⟩]
theorem checked27836 : checkPrefixCuts (2^48) 3652452353 9 Manual.Count131072.C027836.packed 128 cuts27836 = true := by
 decide +kernel
def pointBounds27836 : List (Nat × Nat × Nat) := [(3652481024,104273663332499,104274046119035)]
theorem point_links_checked27836 : (cuts27836.take 1).map (fun c => (3652452353-1+2*2^9*c.k,104273562532355+c.lower,104273945318834+c.upper)) = pointBounds27836 := by
 decide +kernel
def cuts27837 : List PrefixCut := [⟨12,40996841,40996865⟩,
⟨124,444947448,444947697⟩,
⟨128,461052809,461053067⟩]
theorem checked27837 : checkPrefixCuts (2^48) 3652583425 9 Manual.Count131072.C027837.packed 128 cuts27837 = true := by
 decide +kernel
def pointBounds27837 : List (Nat × Nat × Nat) := [(3652595712,104274057662909,104274440449664),(3652710400,104274461613516,104274844400496)]
theorem point_links_checked27837 : (cuts27837.take 2).map (fun c => (3652583425-1+2*2^9*c.k,104274016666068+c.lower,104274399452799+c.upper)) = pointBounds27837 := by
 decide +kernel
def cuts27838 : List PrefixCut := [⟨108,379202091,379202308⟩,
⟨128,449477667,449477923⟩]
theorem checked27838 : checkPrefixCuts (2^48) 3652714497 9 Manual.Count131072.C027838.packed 128 cuts27838 = true := by
 decide +kernel
def pointBounds27838 : List (Nat × Nat × Nat) := [(3652825088,104274856920968,104275239708174)]
theorem point_links_checked27838 : (cuts27838.take 1).map (fun c => (3652714497-1+2*2^9*c.k,104274477718877+c.lower,104274860505866+c.upper)) = pointBounds27838 := by
 decide +kernel
def cuts27839 : List PrefixCut := [⟨92,332570803,332570988⟩,
⟨128,463177258,463177517⟩]
theorem checked27839 : checkPrefixCuts (2^48) 3652845569 9 Manual.Count131072.C027839.packed 128 cuts27839 = true := by
 decide +kernel
def pointBounds27839 : List (Nat × Nat × Nat) := [(3652939776,104275259767347,104275642554777)]
theorem point_links_checked27839 : (cuts27839.take 1).map (fun c => (3652845569-1+2*2^9*c.k,104274927196544+c.lower,104275309983789+c.upper)) = pointBounds27839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000244
