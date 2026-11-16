import PlattAssemblyKernel
import PlattCertificates.Count131072.C046048
import PlattCertificates.Count131072.C046049
import PlattCertificates.Count131072.C046050
import PlattCertificates.Count131072.C046051
import PlattCertificates.Count131072.C046052
import PlattCertificates.Count131072.C046053
import PlattCertificates.Count131072.C046054
import PlattCertificates.Count131072.C046055
import PlattCertificates.Count131072.C046056
import PlattCertificates.Count131072.C046057
import PlattCertificates.Count131072.C046058
import PlattCertificates.Count131072.C046059
import PlattCertificates.Count131072.C046060
import PlattCertificates.Count131072.C046061
import PlattCertificates.Count131072.C046062
import PlattCertificates.Count131072.C046063
import PlattCertificates.Count131072.C046064
import PlattCertificates.Count131072.C046065
import PlattCertificates.Count131072.C046066
import PlattCertificates.Count131072.C046067
import PlattCertificates.Count131072.C046068
import PlattCertificates.Count131072.C046069
import PlattCertificates.Count131072.C046070
import PlattCertificates.Count131072.C046071
import PlattCertificates.Count131072.C046072
import PlattCertificates.Count131072.C046073
import PlattCertificates.Count131072.C046074
import PlattCertificates.Count131072.C046075
import PlattCertificates.Count131072.C046076
import PlattCertificates.Count131072.C046077
import PlattCertificates.Count131072.C046078
import PlattCertificates.Count131072.C046079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46048 : List PrefixCut := [⟨64,267931457,267931618⟩]
theorem checked46048 : checkPrefixCuts (2^48) 6039535617 10 Manual.Count131072.C046048.packed 64 cuts46048 = true := by
 decide +kernel
def cuts46049 : List PrefixCut := [⟨16,67016907,67016944⟩,
⟨64,270349049,270349203⟩]
theorem checked46049 : checkPrefixCuts (2^48) 6039666689 10 Manual.Count131072.C046049.packed 64 cuts46049 = true := by
 decide +kernel
def pointBounds46049 : List (Nat × Nat × Nat) := [(6039699456,110630625211544,110631011746724)]
theorem point_links_checked46049 : (cuts46049.take 1).map (fun c => (6039666689-1+2*2^10*c.k,110630558194637+c.lower,110630944729780+c.upper)) = pointBounds46049 := by
 decide +kernel
def cuts46050 : List PrefixCut := [⟨45,190746121,190746229⟩,
⟨64,272999541,272999696⟩]
theorem checked46050 : checkPrefixCuts (2^48) 6039797761 10 Manual.Count131072.C046050.packed 64 cuts46050 = true := by
 decide +kernel
def pointBounds46050 : List (Nat × Nat × Nat) := [(6039889920,110631019289807,110631405825212)]
theorem point_links_checked46050 : (cuts46050.take 1).map (fun c => (6039797761-1+2*2^10*c.k,110630828543686+c.lower,110631215078983+c.upper)) = pointBounds46050 := by
 decide +kernel
def cuts46051 : List PrefixCut := [⟨64,266748980,266749135⟩]
theorem checked46051 : checkPrefixCuts (2^48) 6039928833 10 Manual.Count131072.C046051.packed 64 cuts46051 = true := by
 decide +kernel
def cuts46052 : List PrefixCut := [⟨10,42034339,42034362⟩,
⟨64,267582017,267582170⟩]
theorem checked46052 : checkPrefixCuts (2^48) 6040059905 10 Manual.Count131072.C046052.packed 64 cuts46052 = true := by
 decide +kernel
def pointBounds46052 : List (Nat × Nat × Nat) := [(6040080384,110631410326546,110631796862176)]
theorem point_links_checked46052 : (cuts46052.take 1).map (fun c => (6040059905-1+2*2^10*c.k,110631368292207+c.lower,110631754827814+c.upper)) = pointBounds46052 := by
 decide +kernel
def cuts46053 : List PrefixCut := [⟨39,167340680,167340776⟩,
⟨64,275637959,275638117⟩]
theorem checked46053 : checkPrefixCuts (2^48) 6040190977 10 Manual.Count131072.C046053.packed 64 cuts46053 = true := by
 decide +kernel
def pointBounds46053 : List (Nat × Nat × Nat) := [(6040270848,110631803214904,110632189750760)]
theorem point_links_checked46053 : (cuts46053.take 1).map (fun c => (6040190977-1+2*2^10*c.k,110631635874224+c.lower,110632022409984+c.upper)) = pointBounds46053 := by
 decide +kernel
def cuts46054 : List PrefixCut := [⟨64,268875127,268875284⟩]
theorem checked46054 : checkPrefixCuts (2^48) 6040322049 10 Manual.Count131072.C046054.packed 64 cuts46054 = true := by
 decide +kernel
def cuts46055 : List PrefixCut := [⟨4,15796815,15796825⟩,
⟨64,268449933,268450092⟩]
theorem checked46055 : checkPrefixCuts (2^48) 6040453121 10 Manual.Count131072.C046055.packed 64 cuts46055 = true := by
 decide +kernel
def pointBounds46055 : List (Nat × Nat × Nat) := [(6040461312,110632196184125,110632582720210)]
theorem point_links_checked46055 : (cuts46055.take 1).map (fun c => (6040453121-1+2*2^10*c.k,110632180387310+c.lower,110632566923385+c.upper)) = pointBounds46055 := by
 decide +kernel
def cuts46056 : List PrefixCut := [⟨33,137973824,137973904⟩,
⟨64,268211137,268211290⟩]
theorem checked46056 : checkPrefixCuts (2^48) 6040584193 10 Manual.Count131072.C046056.packed 64 cuts46056 = true := by
 decide +kernel
def pointBounds46056 : List (Nat × Nat × Nat) := [(6040651776,110632586811067,110632973347381)]
theorem point_links_checked46056 : (cuts46056.take 1).map (fun c => (6040584193-1+2*2^10*c.k,110632448837243+c.lower,110632835373477+c.upper)) = pointBounds46056 := by
 decide +kernel
def cuts46057 : List PrefixCut := [⟨62,261728618,261728768⟩,
⟨64,270208961,270209115⟩]
theorem checked46057 : checkPrefixCuts (2^48) 6040715265 10 Manual.Count131072.C046057.packed 64 cuts46057 = true := by
 decide +kernel
def pointBounds46057 : List (Nat × Nat × Nat) := [(6040842240,110632978776998,110633365313535)]
theorem point_links_checked46057 : (cuts46057.take 1).map (fun c => (6040715265-1+2*2^10*c.k,110632717048380+c.lower,110633103584767+c.upper)) = pointBounds46057 := by
 decide +kernel
def cuts46058 : List PrefixCut := [⟨64,269783718,269783873⟩]
theorem checked46058 : checkPrefixCuts (2^48) 6040846337 10 Manual.Count131072.C046058.packed 64 cuts46058 = true := by
 decide +kernel
def cuts46059 : List PrefixCut := [⟨27,112384856,112384918⟩,
⟨64,269125547,269125697⟩]
theorem checked46059 : checkPrefixCuts (2^48) 6040977409 10 Manual.Count131072.C046059.packed 64 cuts46059 = true := by
 decide +kernel
def pointBounds46059 : List (Nat × Nat × Nat) := [(6041032704,110633369425915,110633755962673)]
theorem point_links_checked46059 : (cuts46059.take 1).map (fun c => (6040977409-1+2*2^10*c.k,110633257041059+c.lower,110633643577755+c.upper)) = pointBounds46059 := by
 decide +kernel
def cuts46060 : List PrefixCut := [⟨56,239626819,239626957⟩,
⟨64,274943787,274943945⟩]
theorem checked46060 : checkPrefixCuts (2^48) 6041108481 10 Manual.Count131072.C046060.packed 64 cuts46060 = true := by
 decide +kernel
def pointBounds46060 : List (Nat × Nat × Nat) := [(6041223168,110633765793425,110634152330409)]
theorem point_links_checked46060 : (cuts46060.take 1).map (fun c => (6041108481-1+2*2^10*c.k,110633526166606+c.lower,110633912703452+c.upper)) = pointBounds46060 := by
 decide +kernel
def cuts46061 : List PrefixCut := [⟨64,273819620,273819778⟩]
theorem checked46061 : checkPrefixCuts (2^48) 6041239553 10 Manual.Count131072.C046061.packed 64 cuts46061 = true := by
 decide +kernel
def cuts46062 : List PrefixCut := [⟨21,90386668,90386715⟩,
⟨64,271856890,271857045⟩]
theorem checked46062 : checkPrefixCuts (2^48) 6041370625 10 Manual.Count131072.C046062.packed 64 cuts46062 = true := by
 decide +kernel
def pointBounds46062 : List (Nat × Nat × Nat) := [(6041413632,110634165316681,110634551853890)]
theorem point_links_checked46062 : (cuts46062.take 1).map (fun c => (6041370625-1+2*2^10*c.k,110634074930013+c.lower,110634461467175+c.upper)) = pointBounds46062 := by
 decide +kernel
def cuts46063 : List PrefixCut := [⟨50,213288211,213288326⟩,
⟨64,271431686,271431830⟩]
theorem checked46063 : checkPrefixCuts (2^48) 6041501697 10 Manual.Count131072.C046063.packed 64 cuts46063 = true := by
 decide +kernel
def pointBounds46063 : List (Nat × Nat × Nat) := [(6041604096,110634560075114,110634946612546)]
theorem point_links_checked46063 : (cuts46063.take 1).map (fun c => (6041501697-1+2*2^10*c.k,110634346786903+c.lower,110634733324220+c.upper)) = pointBounds46063 := by
 decide +kernel
def cuts46064 : List PrefixCut := [⟨64,270167884,270168034⟩]
theorem checked46064 : checkPrefixCuts (2^48) 6041632769 10 Manual.Count131072.C046064.packed 64 cuts46064 = true := by
 decide +kernel
def cuts46065 : List PrefixCut := [⟨15,64571082,64571119⟩,
⟨64,271746020,271746179⟩]
theorem checked46065 : checkPrefixCuts (2^48) 6041763841 10 Manual.Count131072.C046065.packed 64 cuts46065 = true := by
 decide +kernel
def pointBounds46065 : List (Nat × Nat × Nat) := [(6041794560,110634952957555,110635339495203)]
theorem point_links_checked46065 : (cuts46065.take 1).map (fun c => (6041763841-1+2*2^10*c.k,110634888386473+c.lower,110635274924084+c.upper)) = pointBounds46065 := by
 decide +kernel
def cuts46066 : List PrefixCut := [⟨44,183831670,183831778⟩,
⟨64,270202737,270202890⟩]
theorem checked46066 : checkPrefixCuts (2^48) 6041894913 10 Manual.Count131072.C046066.packed 64 cuts46066 = true := by
 decide +kernel
def pointBounds46066 : List (Nat × Nat × Nat) := [(6041985024,110635343964163,110635730502041)]
theorem point_links_checked46066 : (cuts46066.take 1).map (fun c => (6041894913-1+2*2^10*c.k,110635160132493+c.lower,110635546670263+c.upper)) = pointBounds46066 := by
 decide +kernel
def cuts46067 : List PrefixCut := [⟨64,271035469,271035618⟩]
theorem checked46067 : checkPrefixCuts (2^48) 6042025985 10 Manual.Count131072.C046067.packed 64 cuts46067 = true := by
 decide +kernel
def cuts46068 : List PrefixCut := [⟨9,37966854,37966876⟩,
⟨64,271588577,271588733⟩]
theorem checked46068 : checkPrefixCuts (2^48) 6042157057 10 Manual.Count131072.C046068.packed 64 cuts46068 = true := by
 decide +kernel
def pointBounds46068 : List (Nat × Nat × Nat) := [(6042175488,110635739337553,110636125875647)]
theorem point_links_checked46068 : (cuts46068.take 1).map (fun c => (6042157057-1+2*2^10*c.k,110635701370699+c.lower,110636087908771+c.upper)) = pointBounds46068 := by
 decide +kernel
def cuts46069 : List PrefixCut := [⟨38,158757788,158757882⟩,
⟨64,270418087,270418245⟩]
theorem checked46069 : checkPrefixCuts (2^48) 6042288129 10 Manual.Count131072.C046069.packed 64 cuts46069 = true := by
 decide +kernel
def pointBounds46069 : List (Nat × Nat × Nat) := [(6042365952,110636131717064,110636518255386)]
theorem point_links_checked46069 : (cuts46069.take 1).map (fun c => (6042288129-1+2*2^10*c.k,110635972959276+c.lower,110636359497504+c.upper)) = pointBounds46069 := by
 decide +kernel
def cuts46070 : List PrefixCut := [⟨64,270971234,270971391⟩]
theorem checked46070 : checkPrefixCuts (2^48) 6042419201 10 Manual.Count131072.C046070.packed 64 cuts46070 = true := by
 decide +kernel
def cuts46071 : List PrefixCut := [⟨3,13415649,13415656⟩,
⟨64,272083272,272083426⟩]
theorem checked46071 : checkPrefixCuts (2^48) 6042550273 10 Manual.Count131072.C046071.packed 64 cuts46071 = true := by
 decide +kernel
def pointBounds46071 : List (Nat × Nat × Nat) := [(6042556416,110636527764246,110636914302796)]
theorem point_links_checked46071 : (cuts46071.take 1).map (fun c => (6042550273-1+2*2^10*c.k,110636514348597+c.lower,110636900887140+c.upper)) = pointBounds46071 := by
 decide +kernel
def cuts46072 : List PrefixCut := [⟨32,139602882,139602960⟩,
⟨64,274639363,274639518⟩]
theorem checked46072 : checkPrefixCuts (2^48) 6042681345 10 Manual.Count131072.C046072.packed 64 cuts46072 = true := by
 decide +kernel
def pointBounds46072 : List (Nat × Nat × Nat) := [(6042746880,110636926034751,110637312573526)]
theorem point_links_checked46072 : (cuts46072.take 1).map (fun c => (6042681345-1+2*2^10*c.k,110636786431869+c.lower,110637172970566+c.upper)) = pointBounds46072 := by
 decide +kernel
def cuts46073 : List PrefixCut := [⟨61,260752791,260752936⟩,
⟨64,272723627,272723779⟩]
theorem checked46073 : checkPrefixCuts (2^48) 6042812417 10 Manual.Count131072.C046073.packed 64 cuts46073 = true := by
 decide +kernel
def pointBounds46073 : List (Nat × Nat × Nat) := [(6042937344,110637321824023,110637708363020)]
theorem point_links_checked46073 : (cuts46073.take 1).map (fun c => (6042812417-1+2*2^10*c.k,110637061071232+c.lower,110637447610084+c.upper)) = pointBounds46073 := by
 decide +kernel
def cuts46074 : List PrefixCut := [⟨64,275698736,275698898⟩]
theorem checked46074 : checkPrefixCuts (2^48) 6042943489 10 Manual.Count131072.C046074.packed 64 cuts46074 = true := by
 decide +kernel
def cuts46075 : List PrefixCut := [⟨26,107222302,107222365⟩,
⟨64,268985568,268985723⟩]
theorem checked46075 : checkPrefixCuts (2^48) 6043074561 10 Manual.Count131072.C046075.packed 64 cuts46075 = true := by
 decide +kernel
def pointBounds46075 : List (Nat × Nat × Nat) := [(6043127808,110637716715897,110638103255126)]
theorem point_links_checked46075 : (cuts46075.take 1).map (fun c => (6043074561-1+2*2^10*c.k,110637609493595+c.lower,110637996032761+c.upper)) = pointBounds46075 := by
 decide +kernel
def cuts46076 : List PrefixCut := [⟨55,233255866,233256002⟩,
⟨64,272286676,272286834⟩]
theorem checked46076 : checkPrefixCuts (2^48) 6043205633 10 Manual.Count131072.C046076.packed 64 cuts46076 = true := by
 decide +kernel
def pointBounds46076 : List (Nat × Nat × Nat) := [(6043318272,110638111735029,110638498274486)]
theorem point_links_checked46076 : (cuts46076.take 1).map (fun c => (6043205633-1+2*2^10*c.k,110637878479163+c.lower,110638265018484+c.upper)) = pointBounds46076 := by
 decide +kernel
def cuts46077 : List PrefixCut := [⟨64,274143796,274143948⟩]
theorem checked46077 : checkPrefixCuts (2^48) 6043336705 10 Manual.Count131072.C046077.packed 64 cuts46077 = true := by
 decide +kernel
def cuts46078 : List PrefixCut := [⟨20,82856759,82856810⟩,
⟨64,268222869,268223027⟩]
theorem checked46078 : checkPrefixCuts (2^48) 6043467777 10 Manual.Count131072.C046078.packed 64 cuts46078 = true := by
 decide +kernel
def pointBounds46078 : List (Nat × Nat × Nat) := [(6043508736,110638507766394,110638894306076)]
theorem point_links_checked46078 : (cuts46078.take 1).map (fun c => (6043467777-1+2*2^10*c.k,110638424909635+c.lower,110638811449266+c.upper)) = pointBounds46078 := by
 decide +kernel
def cuts46079 : List PrefixCut := [⟨49,208044562,208044683⟩,
⟨64,274131878,274132036⟩]
theorem checked46079 : checkPrefixCuts (2^48) 6043598849 10 Manual.Count131072.C046079.packed 64 cuts46079 = true := by
 decide +kernel
def pointBounds46079 : List (Nat × Nat × Nat) := [(6043699200,110638901177066,110639287716976)]
theorem point_links_checked46079 : (cuts46079.take 1).map (fun c => (6043598849-1+2*2^10*c.k,110638693132504+c.lower,110639079672293+c.upper)) = pointBounds46079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000189
