import PlattAssemblyKernel
import PlattCertificates.Count131072.C017776
import PlattCertificates.Count131072.C017777
import PlattCertificates.Count131072.C017778
import PlattCertificates.Count131072.C017779
import PlattCertificates.Count131072.C017780
import PlattCertificates.Count131072.C017781
import PlattCertificates.Count131072.C017782
import PlattCertificates.Count131072.C017783
import PlattCertificates.Count131072.C017784
import PlattCertificates.Count131072.C017785
import PlattCertificates.Count131072.C017786
import PlattCertificates.Count131072.C017787
import PlattCertificates.Count131072.C017788
import PlattCertificates.Count131072.C017789
import PlattCertificates.Count131072.C017790
import PlattCertificates.Count131072.C017791
import PlattCertificates.Count131072.C017792
import PlattCertificates.Count131072.C017793
import PlattCertificates.Count131072.C017794
import PlattCertificates.Count131072.C017795
import PlattCertificates.Count131072.C017796
import PlattCertificates.Count131072.C017797
import PlattCertificates.Count131072.C017798
import PlattCertificates.Count131072.C017799
import PlattCertificates.Count131072.C017800
import PlattCertificates.Count131072.C017801
import PlattCertificates.Count131072.C017802
import PlattCertificates.Count131072.C017803
import PlattCertificates.Count131072.C017804
import PlattCertificates.Count131072.C017805
import PlattCertificates.Count131072.C017806
import PlattCertificates.Count131072.C017807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000243
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17776 : List PrefixCut := [⟨68,381586852,381587088⟩,
⟨128,732410138,732410586⟩]
theorem checked17776 : checkPrefixCuts (2^48) 2333868033 9 Manual.Count131072.C017776.packed 128 cuts17776 = true := by
 decide +kernel
def pointBounds17776 : List (Nat × Nat × Nat) := [(2333937664,98489583829965,98489963280906)]
theorem point_links_checked17776 : (cuts17776.take 1).map (fun c => (2333868033-1+2*2^9*c.k,98489202243113+c.lower,98489581693818+c.upper)) = pointBounds17776 := by
 decide +kernel
def cuts17777 : List PrefixCut := [⟨12,69222893,69222933⟩,
⟨84,480211171,480211466⟩,
⟨128,735142815,735143270⟩]
theorem checked17777 : checkPrefixCuts (2^48) 2333999105 9 Manual.Count131072.C017777.packed 128 cuts17777 = true := by
 decide +kernel
def pointBounds17777 : List (Nat × Nat × Nat) := [(2334011392,98490003876144,98490383327337),(2334085120,98490414864422,98490794315870)]
theorem point_links_checked17777 : (cuts17777.take 2).map (fun c => (2333999105-1+2*2^9*c.k,98489934653251+c.lower,98490314104404+c.upper)) = pointBounds17777 := by
 decide +kernel
def cuts17778 : List PrefixCut := [⟨28,160023159,160023257⟩,
⟨100,574120736,574121090⟩,
⟨128,734860406,734860862⟩]
theorem checked17778 : checkPrefixCuts (2^48) 2334130177 9 Manual.Count131072.C017778.packed 128 cuts17778 = true := by
 decide +kernel
def pointBounds17778 : List (Nat × Nat × Nat) := [(2334158848,98490829819225,98491209270931),(2334232576,98491243916802,98491623368764)]
theorem point_links_checked17778 : (cuts17778.take 2).map (fun c => (2334130177-1+2*2^9*c.k,98490669796066+c.lower,98491049247674+c.upper)) = pointBounds17778 := by
 decide +kernel
def cuts17779 : List PrefixCut := [⟨44,247195103,247195255⟩,
⟨116,663195791,663196195⟩,
⟨128,728307743,728308187⟩]
theorem checked17779 : checkPrefixCuts (2^48) 2334261249 9 Manual.Count131072.C017779.packed 128 cuts17779 = true := by
 decide +kernel
def pointBounds17779 : List (Nat × Nat × Nat) := [(2334306304,98491651851575,98492031303791),(2334380032,98492067852263,98492447304731)]
theorem point_links_checked17779 : (cuts17779.take 2).map (fun c => (2334261249-1+2*2^9*c.k,98491404656472+c.lower,98491784108536+c.upper)) = pointBounds17779 := by
 decide +kernel
def cuts17780 : List PrefixCut := [⟨60,339300239,339300447⟩,
⟨128,734657156,734657606⟩]
theorem checked17780 : checkPrefixCuts (2^48) 2334392321 9 Manual.Count131072.C017780.packed 128 cuts17780 = true := by
 decide +kernel
def pointBounds17780 : List (Nat × Nat × Nat) := [(2334453760,98492472264454,98492851717170)]
theorem point_links_checked17780 : (cuts17780.take 1).map (fun c => (2334392321-1+2*2^9*c.k,98492132964215+c.lower,98492512416723+c.upper)) = pointBounds17780 := by
 decide +kernel
def cuts17781 : List PrefixCut := [⟨4,23511246,23511261⟩,
⟨76,438749075,438749342⟩,
⟨128,738233072,738233526⟩]
theorem checked17781 : checkPrefixCuts (2^48) 2334523393 9 Manual.Count131072.C017781.packed 128 cuts17781 = true := by
 decide +kernel
def pointBounds17781 : List (Nat × Nat × Nat) := [(2334527488,98492891132617,98493270585590),(2334601216,98493306370446,98493685823671)]
theorem point_links_checked17781 : (cuts17781.take 2).map (fun c => (2334523393-1+2*2^9*c.k,98492867621371+c.lower,98493247074329+c.upper)) = pointBounds17781 := by
 decide +kernel
def cuts17782 : List PrefixCut := [⟨20,112606121,112606192⟩,
⟨92,523839227,523839557⟩,
⟨128,732766250,732766703⟩]
theorem checked17782 : checkPrefixCuts (2^48) 2334654465 9 Manual.Count131072.C017782.packed 128 cuts17782 = true := by
 decide +kernel
def pointBounds17782 : List (Nat × Nat × Nat) := [(2334674944,98493718460564,98494097914047),(2334748672,98494129693670,98494509147412)]
theorem point_links_checked17782 : (cuts17782.take 2).map (fun c => (2334654465-1+2*2^9*c.k,98493605854443+c.lower,98493985307855+c.upper)) = pointBounds17782 := by
 decide +kernel
def cuts17783 : List PrefixCut := [⟨36,205307048,205307182⟩,
⟨108,616514241,616514619⟩,
⟨128,729349810,729350253⟩]
theorem checked17783 : checkPrefixCuts (2^48) 2334785537 9 Manual.Count131072.C017783.packed 128 cuts17783 = true := by
 decide +kernel
def pointBounds17783 : List (Nat × Nat × Nat) := [(2334822400,98494543927741,98494923381740),(2334896128,98494955134934,98495334589177)]
theorem point_links_checked17783 : (cuts17783.take 2).map (fun c => (2334785537-1+2*2^9*c.k,98494338620693+c.lower,98494718074558+c.upper)) = pointBounds17783 := by
 decide +kernel
def cuts17784 : List PrefixCut := [⟨52,300287335,300287524⟩,
⟨124,709901389,709901826⟩,
⟨128,732684135,732684586⟩]
theorem checked17784 : checkPrefixCuts (2^48) 2334916609 9 Manual.Count131072.C017784.packed 128 cuts17784 = true := by
 decide +kernel
def pointBounds17784 : List (Nat × Nat × Nat) := [(2334969856,98495368257838,98495747712335),(2335043584,98495777871892,98496157326637)]
theorem point_links_checked17784 : (cuts17784.take 2).map (fun c => (2334916609-1+2*2^9*c.k,98495067970503+c.lower,98495447424811+c.upper)) = pointBounds17784 := by
 decide +kernel
def cuts17785 : List PrefixCut := [⟨68,384648675,384648914⟩,
⟨128,726615942,726616381⟩]
theorem checked17785 : checkPrefixCuts (2^48) 2335047681 9 Manual.Count131072.C017785.packed 128 cuts17785 = true := by
 decide +kernel
def pointBounds17785 : List (Nat × Nat × Nat) := [(2335117312,98496185303313,98496564758311)]
theorem point_links_checked17785 : (cuts17785.take 1).map (fun c => (2335047681-1+2*2^9*c.k,98495800654638+c.lower,98496180109397+c.upper)) = pointBounds17785 := by
 decide +kernel
def cuts17786 : List PrefixCut := [⟨12,70272745,70272788⟩,
⟨84,482499866,482500161⟩,
⟨128,734168937,734169378⟩]
theorem checked17786 : checkPrefixCuts (2^48) 2335178753 9 Manual.Count131072.C017786.packed 128 cuts17786 = true := by
 decide +kernel
def pointBounds17786 : List (Nat × Nat × Nat) := [(2335191040,98496597543325,98496976998566),(2335264768,98497009770446,98497389225939)]
theorem point_links_checked17786 : (cuts17786.take 2).map (fun c => (2335178753-1+2*2^9*c.k,98496527270580+c.lower,98496906725778+c.upper)) = pointBounds17786 := by
 decide +kernel
def cuts17787 : List PrefixCut := [⟨28,163437651,163437753⟩,
⟨100,586486114,586486476⟩,
⟨128,749314023,749314483⟩]
theorem checked17787 : checkPrefixCuts (2^48) 2335309825 9 Manual.Count131072.C017787.packed 128 cuts17787 = true := by
 decide +kernel
def pointBounds17787 : List (Nat × Nat × Nat) := [(2335338496,98497424877168,98497804332909),(2335412224,98497847925631,98498227381632)]
theorem point_links_checked17787 : (cuts17787.take 2).map (fun c => (2335309825-1+2*2^9*c.k,98497261439517+c.lower,98497640895156+c.upper)) = pointBounds17787 := by
 decide +kernel
def cuts17788 : List PrefixCut := [⟨44,262497032,262497189⟩,
⟨116,668043507,668043913⟩,
⟨128,736497043,736497491⟩]
theorem checked17788 : checkPrefixCuts (2^48) 2335440897 9 Manual.Count131072.C017788.packed 128 cuts17788 = true := by
 decide +kernel
def pointBounds17788 : List (Nat × Nat × Nat) := [(2335485952,98498273250572,98498652706828),(2335559680,98498678797047,98499058253552)]
theorem point_links_checked17788 : (cuts17788.take 2).map (fun c => (2335440897-1+2*2^9*c.k,98498010753540+c.lower,98498390209639+c.upper)) = pointBounds17788 := by
 decide +kernel
def cuts17789 : List PrefixCut := [⟨60,340213579,340213788⟩,
⟨128,722355596,722356044⟩]
theorem checked17789 : checkPrefixCuts (2^48) 2335571969 9 Manual.Count131072.C017789.packed 128 cuts17789 = true := by
 decide +kernel
def pointBounds17789 : List (Nat × Nat × Nat) := [(2335633408,98499087464162,98499466920918)]
theorem point_links_checked17789 : (cuts17789.take 1).map (fun c => (2335571969-1+2*2^9*c.k,98498747250583+c.lower,98499126707130+c.upper)) = pointBounds17789 := by
 decide +kernel
def cuts17790 : List PrefixCut := [⟨4,21571218,21571232⟩,
⟨76,430091986,430092248⟩,
⟨128,725448079,725448523⟩]
theorem checked17790 : checkPrefixCuts (2^48) 2335703041 9 Manual.Count131072.C017790.packed 128 cuts17790 = true := by
 decide +kernel
def pointBounds17790 : List (Nat × Nat × Nat) := [(2335707136,98499491177397,98499870634406),(2335780864,98499899698165,98500279155422)]
theorem point_links_checked17790 : (cuts17790.take 2).map (fun c => (2335703041-1+2*2^9*c.k,98499469606179+c.lower,98499849063174+c.upper)) = pointBounds17790 := by
 decide +kernel
def cuts17791 : List PrefixCut := [⟨20,112428760,112428830⟩,
⟨92,526346180,526346501⟩,
⟨128,735649709,735650154⟩]
theorem checked17791 : checkPrefixCuts (2^48) 2335834113 9 Manual.Count131072.C017791.packed 128 cuts17791 = true := by
 decide +kernel
def pointBounds17791 : List (Nat × Nat × Nat) := [(2335854592,98500307483018,98500686940527),(2335928320,98500721400438,98501100858198)]
theorem point_links_checked17791 : (cuts17791.take 2).map (fun c => (2335834113-1+2*2^9*c.k,98500195054258+c.lower,98500574511697+c.upper)) = pointBounds17791 := by
 decide +kernel
def cuts17792 : List PrefixCut := [⟨36,203998452,203998577⟩,
⟨108,624998907,624999293⟩,
⟨128,738500456,738500911⟩]
theorem checked17792 : checkPrefixCuts (2^48) 2335965185 9 Manual.Count131072.C017792.packed 128 cuts17792 = true := by
 decide +kernel
def pointBounds17792 : List (Nat × Nat × Nat) := [(2336002048,98501134702419,98501514160428),(2336075776,98501555702874,98501935161144)]
theorem point_links_checked17792 : (cuts17792.take 2).map (fun c => (2335965185-1+2*2^9*c.k,98500930703967+c.lower,98501310161851+c.upper)) = pointBounds17792 := by
 decide +kernel
def cuts17793 : List PrefixCut := [⟨52,300858636,300858824⟩,
⟨124,700988529,700988969⟩,
⟨128,722675426,722675881⟩]
theorem checked17793 : checkPrefixCuts (2^48) 2336096257 9 Manual.Count131072.C017793.packed 128 cuts17793 = true := by
 decide +kernel
def pointBounds17793 : List (Nat × Nat × Nat) := [(2336149504,98501970063059,98502349521586),(2336223232,98502370192952,98502749651731)]
theorem point_links_checked17793 : (cuts17793.take 2).map (fun c => (2336096257-1+2*2^9*c.k,98501669204423+c.lower,98502048662762+c.upper)) = pointBounds17793 := by
 decide +kernel
def cuts17794 : List PrefixCut := [⟨68,391201406,391201647⟩,
⟨128,736007927,736008382⟩]
theorem checked17794 : checkPrefixCuts (2^48) 2336227329 9 Manual.Count131072.C017794.packed 128 cuts17794 = true := by
 decide +kernel
def pointBounds17794 : List (Nat × Nat × Nat) := [(2336296960,98502783081255,98503162540290)]
theorem point_links_checked17794 : (cuts17794.take 1).map (fun c => (2336227329-1+2*2^9*c.k,98502391879849+c.lower,98502771338643+c.upper)) = pointBounds17794 := by
 decide +kernel
def cuts17795 : List PrefixCut := [⟨12,70719168,70719210⟩,
⟨84,479123889,479124183⟩,
⟨128,735002807,735003257⟩]
theorem checked17795 : checkPrefixCuts (2^48) 2336358401 9 Manual.Count131072.C017795.packed 128 cuts17795 = true := by
 decide +kernel
def pointBounds17795 : List (Nat × Nat × Nat) := [(2336370688,98503198606944,98503578066235),(2336444416,98503607011665,98503986471208)]
theorem point_links_checked17795 : (cuts17795.take 2).map (fun c => (2336358401-1+2*2^9*c.k,98503127887776+c.lower,98503507347025+c.upper)) = pointBounds17795 := by
 decide +kernel
def cuts17796 : List PrefixCut := [⟨28,160102508,160102608⟩,
⟨100,568120041,568120397⟩,
⟨128,727613213,727613669⟩]
theorem checked17796 : checkPrefixCuts (2^48) 2336489473 9 Manual.Count131072.C017796.packed 128 cuts17796 = true := by
 decide +kernel
def pointBounds17796 : List (Nat × Nat × Nat) := [(2336518144,98504022993091,98504402452890),(2336591872,98504431010624,98504810470679)]
theorem point_links_checked17796 : (cuts17796.take 2).map (fun c => (2336489473-1+2*2^9*c.k,98503862890583+c.lower,98504242350282+c.upper)) = pointBounds17796 := by
 decide +kernel
def cuts17797 : List PrefixCut := [⟨44,249475179,249475334⟩,
⟨116,652166915,652167315⟩,
⟨128,722272277,722272720⟩]
theorem checked17797 : checkPrefixCuts (2^48) 2336620545 9 Manual.Count131072.C017797.packed 128 cuts17797 = true := by
 decide +kernel
def pointBounds17797 : List (Nat × Nat × Nat) := [(2336665600,98504839978975,98505219439285),(2336739328,98505242670711,98505622131266)]
theorem point_links_checked17797 : (cuts17797.take 2).map (fun c => (2336620545-1+2*2^9*c.k,98504590503796+c.lower,98504969963951+c.upper)) = pointBounds17797 := by
 decide +kernel
def cuts17798 : List PrefixCut := [⟨60,351123506,351123722⟩,
⟨128,737649649,737650105⟩]
theorem checked17798 : checkPrefixCuts (2^48) 2336751617 9 Manual.Count131072.C017798.packed 128 cuts17798 = true := by
 decide +kernel
def pointBounds17798 : List (Nat × Nat × Nat) := [(2336813056,98505663899579,98506043360393)]
theorem point_links_checked17798 : (cuts17798.take 1).map (fun c => (2336751617-1+2*2^9*c.k,98505312776073+c.lower,98505692236671+c.upper)) = pointBounds17798 := by
 decide +kernel
def cuts17799 : List PrefixCut := [⟨4,24330651,24330665⟩,
⟨76,439992414,439992683⟩,
⟨128,732188332,732188778⟩]
theorem checked17799 : checkPrefixCuts (2^48) 2336882689 9 Manual.Count131072.C017799.packed 128 cuts17799 = true := by
 decide +kernel
def pointBounds17799 : List (Nat × Nat × Nat) := [(2336886784,98506074756373,98506454217441),(2336960512,98506490418136,98506869879459)]
theorem point_links_checked17799 : (cuts17799.take 2).map (fun c => (2336882689-1+2*2^9*c.k,98506050425722+c.lower,98506429886776+c.upper)) = pointBounds17799 := by
 decide +kernel
def cuts17800 : List PrefixCut := [⟨20,117912315,117912385⟩,
⟨92,529212100,529212424⟩,
⟨128,736603417,736603866⟩]
theorem checked17800 : checkPrefixCuts (2^48) 2337013761 9 Manual.Count131072.C017800.packed 128 cuts17800 = true := by
 decide +kernel
def pointBounds17800 : List (Nat × Nat × Nat) := [(2337034240,98506900526369,98507279987939),(2337107968,98507311826154,98507691287978)]
theorem point_links_checked17800 : (cuts17800.take 2).map (fun c => (2337013761-1+2*2^9*c.k,98506782614054+c.lower,98507162075554+c.upper)) = pointBounds17800 := by
 decide +kernel
def cuts17801 : List PrefixCut := [⟨36,203052426,203052556⟩,
⟨108,615289655,615290038⟩,
⟨128,730058640,730059092⟩]
theorem checked17801 : checkPrefixCuts (2^48) 2337144833 9 Manual.Count131072.C017801.packed 128 cuts17801 = true := by
 decide +kernel
def pointBounds17801 : List (Nat × Nat × Nat) := [(2337181696,98507722269897,98508101731976),(2337255424,98508134507126,98508513969458)]
theorem point_links_checked17801 : (cuts17801.take 2).map (fun c => (2337144833-1+2*2^9*c.k,98507519217471+c.lower,98507898679420+c.upper)) = pointBounds17801 := by
 decide +kernel
def cuts17802 : List PrefixCut := [⟨52,294685441,294685622⟩,
⟨124,703524861,703525289⟩,
⟨128,726284613,726285054⟩]
theorem checked17802 : checkPrefixCuts (2^48) 2337275905 9 Manual.Count131072.C017802.packed 128 cuts17802 = true := by
 decide +kernel
def pointBounds17802 : List (Nat × Nat × Nat) := [(2337329152,98508543961552,98508923424134),(2337402880,98508952800972,98509332263801)]
theorem point_links_checked17802 : (cuts17802.take 2).map (fun c => (2337275905-1+2*2^9*c.k,98508249276111+c.lower,98508628738512+c.upper)) = pointBounds17802 := by
 decide +kernel
def cuts17803 : List PrefixCut := [⟨68,385584994,385585228⟩,
⟨128,728652188,728652631⟩]
theorem checked17803 : checkPrefixCuts (2^48) 2337406977 9 Manual.Count131072.C017803.packed 128 cuts17803 = true := by
 decide +kernel
def pointBounds17803 : List (Nat × Nat × Nat) := [(2337476608,98509361145718,98509740608794)]
theorem point_links_checked17803 : (cuts17803.take 1).map (fun c => (2337406977-1+2*2^9*c.k,98508975560724+c.lower,98509355023566+c.upper)) = pointBounds17803 := by
 decide +kernel
def cuts17804 : List PrefixCut := [⟨12,65505650,65505691⟩,
⟨84,484541451,484541747⟩,
⟨128,734752405,734752855⟩]
theorem checked17804 : checkPrefixCuts (2^48) 2337538049 9 Manual.Count131072.C017804.packed 128 cuts17804 = true := by
 decide +kernel
def pointBounds17804 : List (Nat × Nat × Nat) := [(2337550336,98509769718562,98510149181888),(2337624064,98510188754363,98510568217944)]
theorem point_links_checked17804 : (cuts17804.take 2).map (fun c => (2337538049-1+2*2^9*c.k,98509704212912+c.lower,98510083676197+c.upper)) = pointBounds17804 := by
 decide +kernel
def cuts17805 : List PrefixCut := [⟨28,155927868,155927963⟩,
⟨100,574455553,574455907⟩,
⟨128,738443556,738444009⟩]
theorem checked17805 : checkPrefixCuts (2^48) 2337669121 9 Manual.Count131072.C017805.packed 128 cuts17805 = true := by
 decide +kernel
def pointBounds17805 : List (Nat × Nat × Nat) := [(2337697792,98510594893185,98510974357015),(2337771520,98511013420870,98511392884959)]
theorem point_links_checked17805 : (cuts17805.take 2).map (fun c => (2337669121-1+2*2^9*c.k,98510438965317+c.lower,98510818429052+c.upper)) = pointBounds17805 := by
 decide +kernel
def cuts17806 : List PrefixCut := [⟨44,259222169,259222325⟩,
⟨116,670981240,670981646⟩,
⟨128,735994633,735995079⟩]
theorem checked17806 : checkPrefixCuts (2^48) 2337800193 9 Manual.Count131072.C017806.packed 128 cuts17806 = true := by
 decide +kernel
def pointBounds17806 : List (Nat × Nat × Nat) := [(2337845248,98511436631042,98511816095386),(2337918976,98511848390113,98512227854707)]
theorem point_links_checked17806 : (cuts17806.take 2).map (fun c => (2337800193-1+2*2^9*c.k,98511177408873+c.lower,98511556873061+c.upper)) = pointBounds17806 := by
 decide +kernel
def cuts17807 : List PrefixCut := [⟨60,336980785,336980991⟩,
⟨128,726442115,726442558⟩]
theorem checked17807 : checkPrefixCuts (2^48) 2337931265 9 Manual.Count131072.C017807.packed 128 cuts17807 = true := by
 decide +kernel
def pointBounds17807 : List (Nat × Nat × Nat) := [(2337992704,98512250384291,98512629849131)]
theorem point_links_checked17807 : (cuts17807.take 1).map (fun c => (2337931265-1+2*2^9*c.k,98511913403506+c.lower,98512292868140+c.upper)) = pointBounds17807 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000243
