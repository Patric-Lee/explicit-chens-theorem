import PlattAssemblyKernel
import PlattCertificates.Count131072.C075056
import PlattCertificates.Count131072.C075057
import PlattCertificates.Count131072.C075058
import PlattCertificates.Count131072.C075059
import PlattCertificates.Count131072.C075060
import PlattCertificates.Count131072.C075061
import PlattCertificates.Count131072.C075062
import PlattCertificates.Count131072.C075063
import PlattCertificates.Count131072.C075064
import PlattCertificates.Count131072.C075065
import PlattCertificates.Count131072.C075066
import PlattCertificates.Count131072.C075067
import PlattCertificates.Count131072.C075068
import PlattCertificates.Count131072.C075069
import PlattCertificates.Count131072.C075070
import PlattCertificates.Count131072.C075071
import PlattCertificates.Count131072.C075072
import PlattCertificates.Count131072.C075073
import PlattCertificates.Count131072.C075074
import PlattCertificates.Count131072.C075075
import PlattCertificates.Count131072.C075076
import PlattCertificates.Count131072.C075077
import PlattCertificates.Count131072.C075078
import PlattCertificates.Count131072.C075079
import PlattCertificates.Count131072.C075080
import PlattCertificates.Count131072.C075081
import PlattCertificates.Count131072.C075082
import PlattCertificates.Count131072.C075083
import PlattCertificates.Count131072.C075084
import PlattCertificates.Count131072.C075085
import PlattCertificates.Count131072.C075086
import PlattCertificates.Count131072.C075087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75056 : List PrefixCut := [⟨64,165022698,165022795⟩]
theorem checked75056 : checkPrefixCuts (2^48) 9841672193 10 Manual.Count131072.C075056.packed 64 cuts75056 = true := by
 decide +kernel
def cuts75057 : List PrefixCut := [⟨50,125524438,125524518⟩,
⟨64,160959335,160959433⟩]
theorem checked75057 : checkPrefixCuts (2^48) 9841803265 10 Manual.Count131072.C075057.packed 64 cuts75057 = true := by
 decide +kernel
def pointBounds75057 : List (Nat × Nat × Nat) := [(9841905664,116668144478968,116668534491941)]
theorem point_links_checked75057 : (cuts75057.take 1).map (fun c => (9841803265-1+2*2^10*c.k,116668018954530+c.lower,116668408967423+c.upper)) = pointBounds75057 := by
 decide +kernel
def cuts75058 : List PrefixCut := [⟨64,163445335,163445438⟩]
theorem checked75058 : checkPrefixCuts (2^48) 9841934337 10 Manual.Count131072.C075058.packed 64 cuts75058 = true := by
 decide +kernel
def cuts75059 : List PrefixCut := [⟨64,163242975,163243068⟩]
theorem checked75059 : checkPrefixCuts (2^48) 9842065409 10 Manual.Count131072.C075059.packed 64 cuts75059 = true := by
 decide +kernel
def cuts75060 : List PrefixCut := [⟨9,22793213,22793228⟩,
⟨64,164642124,164642222⟩]
theorem checked75060 : checkPrefixCuts (2^48) 9842196481 10 Manual.Count131072.C075060.packed 64 cuts75060 = true := by
 decide +kernel
def pointBounds75060 : List (Nat × Nat × Nat) := [(9842214912,116668529395388,116668919408590)]
theorem point_links_checked75060 : (cuts75060.take 1).map (fun c => (9842196481-1+2*2^10*c.k,116668506602175+c.lower,116668896615362+c.upper)) = pointBounds75060 := by
 decide +kernel
def cuts75061 : List PrefixCut := [⟨64,162123282,162123388⟩]
theorem checked75061 : checkPrefixCuts (2^48) 9842327553 10 Manual.Count131072.C075061.packed 64 cuts75061 = true := by
 decide +kernel
def cuts75062 : List PrefixCut := [⟨32,80474576,80474625⟩,
⟨64,160634045,160634143⟩]
theorem checked75062 : checkPrefixCuts (2^48) 9842458625 10 Manual.Count131072.C075062.packed 64 cuts75062 = true := by
 decide +kernel
def pointBounds75062 : List (Nat × Nat × Nat) := [(9842524160,116668913842157,116669303855597)]
theorem point_links_checked75062 : (cuts75062.take 1).map (fun c => (9842458625-1+2*2^10*c.k,116668833367581+c.lower,116669223380972+c.upper)) = pointBounds75062 := by
 decide +kernel
def cuts75063 : List PrefixCut := [⟨64,161689998,161690098⟩]
theorem checked75063 : checkPrefixCuts (2^48) 9842589697 10 Manual.Count131072.C075063.packed 64 cuts75063 = true := by
 decide +kernel
def cuts75064 : List PrefixCut := [⟨55,138181187,138181270⟩,
⟨64,160915729,160915828⟩]
theorem checked75064 : checkPrefixCuts (2^48) 9842720769 10 Manual.Count131072.C075064.packed 64 cuts75064 = true := by
 decide +kernel
def pointBounds75064 : List (Nat × Nat × Nat) := [(9842833408,116669293872811,116669683886483)]
theorem point_links_checked75064 : (cuts75064.take 1).map (fun c => (9842720769-1+2*2^10*c.k,116669155691624+c.lower,116669545705213+c.upper)) = pointBounds75064 := by
 decide +kernel
def cuts75065 : List PrefixCut := [⟨64,164059234,164059329⟩]
theorem checked75065 : checkPrefixCuts (2^48) 9842851841 10 Manual.Count131072.C075065.packed 64 cuts75065 = true := by
 decide +kernel
def cuts75066 : List PrefixCut := [⟨64,163170554,163170654⟩]
theorem checked75066 : checkPrefixCuts (2^48) 9842982913 10 Manual.Count131072.C075066.packed 64 cuts75066 = true := by
 decide +kernel
def cuts75067 : List PrefixCut := [⟨14,35945275,35945297⟩,
⟨64,163225580,163225679⟩]
theorem checked75067 : checkPrefixCuts (2^48) 9843113985 10 Manual.Count131072.C075067.packed 64 cuts75067 = true := by
 decide +kernel
def pointBounds75067 : List (Nat × Nat × Nat) := [(9843142656,116669679782416,116670069796321)]
theorem point_links_checked75067 : (cuts75067.take 1).map (fun c => (9843113985-1+2*2^10*c.k,116669643837141+c.lower,116670033851024+c.upper)) = pointBounds75067 := by
 decide +kernel
def cuts75068 : List PrefixCut := [⟨64,165053531,165053621⟩]
theorem checked75068 : checkPrefixCuts (2^48) 9843245057 10 Manual.Count131072.C075068.packed 64 cuts75068 = true := by
 decide +kernel
def cuts75069 : List PrefixCut := [⟨37,93392093,93392148⟩,
⟨64,160476104,160476202⟩]
theorem checked75069 : checkPrefixCuts (2^48) 9843376129 10 Manual.Count131072.C075069.packed 64 cuts75069 = true := by
 decide +kernel
def pointBounds75069 : List (Nat × Nat × Nat) := [(9843451904,116670065508345,116670455522472)]
theorem point_links_checked75069 : (cuts75069.take 1).map (fun c => (9843376129-1+2*2^10*c.k,116669972116252+c.lower,116670362130324+c.upper)) = pointBounds75069 := by
 decide +kernel
def cuts75070 : List PrefixCut := [⟨64,162589967,162590062⟩]
theorem checked75070 : checkPrefixCuts (2^48) 9843507201 10 Manual.Count131072.C075070.packed 64 cuts75070 = true := by
 decide +kernel
def cuts75071 : List PrefixCut := [⟨60,153266100,153266193⟩,
⟨64,163016733,163016831⟩]
theorem checked75071 : checkPrefixCuts (2^48) 9843638273 10 Manual.Count131072.C075071.packed 64 cuts75071 = true := by
 decide +kernel
def pointBounds75071 : List (Nat × Nat × Nat) := [(9843761152,116670448448423,116670838462781)]
theorem point_links_checked75071 : (cuts75071.take 1).map (fun c => (9843638273-1+2*2^10*c.k,116670295182323+c.lower,116670685196588+c.upper)) = pointBounds75071 := by
 decide +kernel
def cuts75072 : List PrefixCut := [⟨64,164758789,164758888⟩]
theorem checked75072 : checkPrefixCuts (2^48) 9843769345 10 Manual.Count131072.C075072.packed 64 cuts75072 = true := by
 decide +kernel
def cuts75073 : List PrefixCut := [⟨64,164413480,164413579⟩]
theorem checked75073 : checkPrefixCuts (2^48) 9843900417 10 Manual.Count131072.C075073.packed 64 cuts75073 = true := by
 decide +kernel
def cuts75074 : List PrefixCut := [⟨19,47293484,47293513⟩,
⟨64,160980085,160980186⟩]
theorem checked75074 : checkPrefixCuts (2^48) 9844031489 10 Manual.Count131072.C075074.packed 64 cuts75074 = true := by
 decide +kernel
def pointBounds75074 : List (Nat × Nat × Nat) := [(9844070400,116670834664809,116671224679399)]
theorem point_links_checked75074 : (cuts75074.take 1).map (fun c => (9844031489-1+2*2^10*c.k,116670787371325+c.lower,116671177385886+c.upper)) = pointBounds75074 := by
 decide +kernel
def cuts75075 : List PrefixCut := [⟨64,161864334,161864429⟩]
theorem checked75075 : checkPrefixCuts (2^48) 9844162561 10 Manual.Count131072.C075075.packed 64 cuts75075 = true := by
 decide +kernel
def cuts75076 : List PrefixCut := [⟨42,106364355,106364425⟩,
⟨64,162862898,162863003⟩]
theorem checked75076 : checkPrefixCuts (2^48) 9844293633 10 Manual.Count131072.C075076.packed 64 cuts75076 = true := by
 decide +kernel
def pointBounds75076 : List (Nat × Nat × Nat) := [(9844379648,116671216580099,116671606594926)]
theorem point_links_checked75076 : (cuts75076.take 1).map (fun c => (9844293633-1+2*2^10*c.k,116671110215744+c.lower,116671500230501+c.upper)) = pointBounds75076 := by
 decide +kernel
def cuts75077 : List PrefixCut := [⟨64,162374682,162374782⟩]
theorem checked75077 : checkPrefixCuts (2^48) 9844424705 10 Manual.Count131072.C075077.packed 64 cuts75077 = true := by
 decide +kernel
def cuts75078 : List PrefixCut := [⟨64,162915752,162915854⟩]
theorem checked75078 : checkPrefixCuts (2^48) 9844555777 10 Manual.Count131072.C075078.packed 64 cuts75078 = true := by
 decide +kernel
def cuts75079 : List PrefixCut := [⟨1,2659014,2659016⟩,
⟨64,161569790,161569886⟩]
theorem checked75079 : checkPrefixCuts (2^48) 9844686849 10 Manual.Count131072.C075079.packed 64 cuts75079 = true := by
 decide +kernel
def pointBounds75079 : List (Nat × Nat × Nat) := [(9844688896,116671601028090,116671991043156)]
theorem point_links_checked75079 : (cuts75079.take 1).map (fun c => (9844686849-1+2*2^10*c.k,116671598369076+c.lower,116671988384140+c.upper)) = pointBounds75079 := by
 decide +kernel
def cuts75080 : List PrefixCut := [⟨64,164340978,164341073⟩]
theorem checked75080 : checkPrefixCuts (2^48) 9844817921 10 Manual.Count131072.C075080.packed 64 cuts75080 = true := by
 decide +kernel
def cuts75081 : List PrefixCut := [⟨24,61870321,61870355⟩,
⟨64,162766304,162766402⟩]
theorem checked75081 : checkPrefixCuts (2^48) 9844948993 10 Manual.Count131072.C075081.packed 64 cuts75081 = true := by
 decide +kernel
def pointBounds75081 : List (Nat × Nat × Nat) := [(9844998144,116671986150165,116672376165454)]
theorem point_links_checked75081 : (cuts75081.take 1).map (fun c => (9844948993-1+2*2^10*c.k,116671924279844+c.lower,116672314295099+c.upper)) = pointBounds75081 := by
 decide +kernel
def cuts75082 : List PrefixCut := [⟨64,163192981,163193077⟩]
theorem checked75082 : checkPrefixCuts (2^48) 9845080065 10 Manual.Count131072.C075082.packed 64 cuts75082 = true := by
 decide +kernel
def cuts75083 : List PrefixCut := [⟨47,116761118,116761189⟩,
⟨64,160960797,160960894⟩]
theorem checked75083 : checkPrefixCuts (2^48) 9845211137 10 Manual.Count131072.C075083.packed 64 cuts75083 = true := by
 decide +kernel
def pointBounds75083 : List (Nat × Nat × Nat) := [(9845307392,116672367000247,116672757015767)]
theorem point_links_checked75083 : (cuts75083.take 1).map (fun c => (9845211137-1+2*2^10*c.k,116672250239129+c.lower,116672640254578+c.upper)) = pointBounds75083 := by
 decide +kernel
def cuts75084 : List PrefixCut := [⟨64,162959928,162960023⟩]
theorem checked75084 : checkPrefixCuts (2^48) 9845342209 10 Manual.Count131072.C075084.packed 64 cuts75084 = true := by
 decide +kernel
def cuts75085 : List PrefixCut := [⟨64,161499707,161499804⟩]
theorem checked75085 : checkPrefixCuts (2^48) 9845473281 10 Manual.Count131072.C075085.packed 64 cuts75085 = true := by
 decide +kernel
def cuts75086 : List PrefixCut := [⟨6,14408790,14408801⟩,
⟨64,162440974,162441079⟩]
theorem checked75086 : checkPrefixCuts (2^48) 9845604353 10 Manual.Count131072.C075086.packed 64 cuts75086 = true := by
 decide +kernel
def pointBounds75086 : List (Nat × Nat × Nat) := [(9845616640,116672750068351,116673140084100)]
theorem point_links_checked75086 : (cuts75086.take 1).map (fun c => (9845604353-1+2*2^10*c.k,116672735659561+c.lower,116673125675299+c.upper)) = pointBounds75086 := by
 decide +kernel
def cuts75087 : List PrefixCut := [⟨64,163353649,163353758⟩]
theorem checked75087 : checkPrefixCuts (2^48) 9845735425 10 Manual.Count131072.C075087.packed 64 cuts75087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000158
