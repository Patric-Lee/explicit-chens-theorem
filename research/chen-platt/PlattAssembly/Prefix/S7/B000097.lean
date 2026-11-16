import PlattAssemblyKernel
import PlattCertificates.Count131072.C063104
import PlattCertificates.Count131072.C063105
import PlattCertificates.Count131072.C063106
import PlattCertificates.Count131072.C063107
import PlattCertificates.Count131072.C063108
import PlattCertificates.Count131072.C063109
import PlattCertificates.Count131072.C063110
import PlattCertificates.Count131072.C063111
import PlattCertificates.Count131072.C063112
import PlattCertificates.Count131072.C063113
import PlattCertificates.Count131072.C063114
import PlattCertificates.Count131072.C063115
import PlattCertificates.Count131072.C063116
import PlattCertificates.Count131072.C063117
import PlattCertificates.Count131072.C063118
import PlattCertificates.Count131072.C063119
import PlattCertificates.Count131072.C063120
import PlattCertificates.Count131072.C063121
import PlattCertificates.Count131072.C063122
import PlattCertificates.Count131072.C063123
import PlattCertificates.Count131072.C063124
import PlattCertificates.Count131072.C063125
import PlattCertificates.Count131072.C063126
import PlattCertificates.Count131072.C063127
import PlattCertificates.Count131072.C063128
import PlattCertificates.Count131072.C063129
import PlattCertificates.Count131072.C063130
import PlattCertificates.Count131072.C063131
import PlattCertificates.Count131072.C063132
import PlattCertificates.Count131072.C063133
import PlattCertificates.Count131072.C063134
import PlattCertificates.Count131072.C063135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63104 : List PrefixCut := [⟨64,191705233,191705346⟩]
theorem checked63104 : checkPrefixCuts (2^48) 8275099649 10 Manual.Count131072.C063104.packed 64 cuts63104 = true := by
 decide +kernel
def cuts63105 : List PrefixCut := [⟨40,123436715,123436784⟩,
⟨64,196566186,196566297⟩]
theorem checked63105 : checkPrefixCuts (2^48) 8275230721 10 Manual.Count131072.C063105.packed 64 cuts63105 = true := by
 decide +kernel
def pointBounds63105 : List (Nat × Nat × Nat) := [(8275312640,114539263760908,114539652524948)]
theorem point_links_checked63105 : (cuts63105.take 1).map (fun c => (8275230721-1+2*2^10*c.k,114539140324193+c.lower,114539529088164+c.upper)) = pointBounds63105 := by
 decide +kernel
def cuts63106 : List PrefixCut := [⟨64,198467819,198467927⟩]
theorem checked63106 : checkPrefixCuts (2^48) 8275361793 10 Manual.Count131072.C063106.packed 64 cuts63106 = true := by
 decide +kernel
def cuts63107 : List PrefixCut := [⟨39,117752669,117752734⟩,
⟨64,194485173,194485282⟩]
theorem checked63107 : checkPrefixCuts (2^48) 8275492865 10 Manual.Count131072.C063107.packed 64 cuts63107 = true := by
 decide +kernel
def pointBounds63107 : List (Nat × Nat × Nat) := [(8275572736,114539653110867,114540041875122)]
theorem point_links_checked63107 : (cuts63107.take 1).map (fun c => (8275492865-1+2*2^10*c.k,114539535358198+c.lower,114539924122388+c.upper)) = pointBounds63107 := by
 decide +kernel
def cuts63108 : List PrefixCut := [⟨64,194652166,194652278⟩]
theorem checked63108 : checkPrefixCuts (2^48) 8275623937 10 Manual.Count131072.C063108.packed 64 cuts63108 = true := by
 decide +kernel
def cuts63109 : List PrefixCut := [⟨38,118429190,118429258⟩,
⟨64,198084265,198084377⟩]
theorem checked63109 : checkPrefixCuts (2^48) 8275755009 10 Manual.Count131072.C063109.packed 64 cuts63109 = true := by
 decide +kernel
def pointBounds63109 : List (Nat × Nat × Nat) := [(8275832832,114540042924727,114540431689206)]
theorem point_links_checked63109 : (cuts63109.take 1).map (fun c => (8275755009-1+2*2^10*c.k,114539924495537+c.lower,114540313259948+c.upper)) = pointBounds63109 := by
 decide +kernel
def cuts63110 : List PrefixCut := [⟨64,195700345,195700454⟩]
theorem checked63110 : checkPrefixCuts (2^48) 8275886081 10 Manual.Count131072.C063110.packed 64 cuts63110 = true := by
 decide +kernel
def cuts63111 : List PrefixCut := [⟨37,112983728,112983790⟩,
⟨64,197193698,197193811⟩]
theorem checked63111 : checkPrefixCuts (2^48) 8276017153 10 Manual.Count131072.C063111.packed 64 cuts63111 = true := by
 decide +kernel
def pointBounds63111 : List (Nat × Nat × Nat) := [(8276092928,114540431263875,114540820028569)]
theorem point_links_checked63111 : (cuts63111.take 1).map (fun c => (8276017153-1+2*2^10*c.k,114540318280147+c.lower,114540707044779+c.upper)) = pointBounds63111 := by
 decide +kernel
def cuts63112 : List PrefixCut := [⟨64,194367731,194367844⟩]
theorem checked63112 : checkPrefixCuts (2^48) 8276148225 10 Manual.Count131072.C063112.packed 64 cuts63112 = true := by
 decide +kernel
def cuts63113 : List PrefixCut := [⟨36,108899009,108899071⟩,
⟨64,194262641,194262755⟩]
theorem checked63113 : checkPrefixCuts (2^48) 8276279297 10 Manual.Count131072.C063113.packed 64 cuts63113 = true := by
 decide +kernel
def pointBounds63113 : List (Nat × Nat × Nat) := [(8276353024,114540818740585,114541207505505)]
theorem point_links_checked63113 : (cuts63113.take 1).map (fun c => (8276279297-1+2*2^10*c.k,114540709841576+c.lower,114541098606434+c.upper)) = pointBounds63113 := by
 decide +kernel
def cuts63114 : List PrefixCut := [⟨64,194565629,194565739⟩]
theorem checked63114 : checkPrefixCuts (2^48) 8276410369 10 Manual.Count131072.C063114.packed 64 cuts63114 = true := by
 decide +kernel
def cuts63115 : List PrefixCut := [⟨35,108351433,108351492⟩,
⟨64,196467047,196467157⟩]
theorem checked63115 : checkPrefixCuts (2^48) 8276541441 10 Manual.Count131072.C063115.packed 64 cuts63115 = true := by
 decide +kernel
def pointBounds63115 : List (Nat × Nat × Nat) := [(8276613120,114541207021279,114541595786420)]
theorem point_links_checked63115 : (cuts63115.take 1).map (fun c => (8276541441-1+2*2^10*c.k,114541098669846+c.lower,114541487434928+c.upper)) = pointBounds63115 := by
 decide +kernel
def cuts63116 : List PrefixCut := [⟨64,195681748,195681859⟩]
theorem checked63116 : checkPrefixCuts (2^48) 8276672513 10 Manual.Count131072.C063116.packed 64 cuts63116 = true := by
 decide +kernel
def cuts63117 : List PrefixCut := [⟨34,102634756,102634815⟩,
⟨64,193740231,193740343⟩]
theorem checked63117 : checkPrefixCuts (2^48) 8276803585 10 Manual.Count131072.C063117.packed 64 cuts63117 = true := by
 decide +kernel
def pointBounds63117 : List (Nat × Nat × Nat) := [(8276873216,114541593453397,114541982218759)]
theorem point_links_checked63117 : (cuts63117.take 1).map (fun c => (8276803585-1+2*2^10*c.k,114541490818641+c.lower,114541879583944+c.upper)) = pointBounds63117 := by
 decide +kernel
def cuts63118 : List PrefixCut := [⟨64,195675544,195675654⟩]
theorem checked63118 : checkPrefixCuts (2^48) 8276934657 10 Manual.Count131072.C063118.packed 64 cuts63118 = true := by
 decide +kernel
def cuts63119 : List PrefixCut := [⟨33,100557115,100557175⟩,
⟨64,195910485,195910599⟩]
theorem checked63119 : checkPrefixCuts (2^48) 8277065729 10 Manual.Count131072.C063119.packed 64 cuts63119 = true := by
 decide +kernel
def pointBounds63119 : List (Nat × Nat × Nat) := [(8277133312,114541980791531,114542369557116)]
theorem point_links_checked63119 : (cuts63119.take 1).map (fun c => (8277065729-1+2*2^10*c.k,114541880234416+c.lower,114542268999941+c.upper)) = pointBounds63119 := by
 decide +kernel
def cuts63120 : List PrefixCut := [⟨64,195057241,195057353⟩]
theorem checked63120 : checkPrefixCuts (2^48) 8277196801 10 Manual.Count131072.C063120.packed 64 cuts63120 = true := by
 decide +kernel
def cuts63121 : List PrefixCut := [⟨32,98173564,98173617⟩,
⟨64,196210325,196210437⟩]
theorem checked63121 : checkPrefixCuts (2^48) 8277327873 10 Manual.Count131072.C063121.packed 64 cuts63121 = true := by
 decide +kernel
def pointBounds63121 : List (Nat × Nat × Nat) := [(8277393408,114542369375706,114542758141510)]
theorem point_links_checked63121 : (cuts63121.take 1).map (fun c => (8277327873-1+2*2^10*c.k,114542271202142+c.lower,114542659967893+c.upper)) = pointBounds63121 := by
 decide +kernel
def cuts63122 : List PrefixCut := [⟨64,198009465,198009582⟩]
theorem checked63122 : checkPrefixCuts (2^48) 8277458945 10 Manual.Count131072.C063122.packed 64 cuts63122 = true := by
 decide +kernel
def cuts63123 : List PrefixCut := [⟨31,93035819,93035867⟩,
⟨64,194469909,194470013⟩]
theorem checked63123 : checkPrefixCuts (2^48) 8277590017 10 Manual.Count131072.C063123.packed 64 cuts63123 = true := by
 decide +kernel
def pointBounds63123 : List (Nat × Nat × Nat) := [(8277653504,114542758457751,114543147223779)]
theorem point_links_checked63123 : (cuts63123.take 1).map (fun c => (8277590017-1+2*2^10*c.k,114542665421932+c.lower,114543054187912+c.upper)) = pointBounds63123 := by
 decide +kernel
def cuts63124 : List PrefixCut := [⟨64,193616739,193616852⟩]
theorem checked63124 : checkPrefixCuts (2^48) 8277721089 10 Manual.Count131072.C063124.packed 64 cuts63124 = true := by
 decide +kernel
def cuts63125 : List PrefixCut := [⟨30,91332720,91332769⟩,
⟨64,197251994,197252101⟩]
theorem checked63125 : checkPrefixCuts (2^48) 8277852161 10 Manual.Count131072.C063125.packed 64 cuts63125 = true := by
 decide +kernel
def pointBounds63125 : List (Nat × Nat × Nat) := [(8277913600,114543144841300,114543533607546)]
theorem point_links_checked63125 : (cuts63125.take 1).map (fun c => (8277852161-1+2*2^10*c.k,114543053508580+c.lower,114543442274777+c.upper)) = pointBounds63125 := by
 decide +kernel
def cuts63126 : List PrefixCut := [⟨64,193644599,193644715⟩]
theorem checked63126 : checkPrefixCuts (2^48) 8277983233 10 Manual.Count131072.C063126.packed 64 cuts63126 = true := by
 decide +kernel
def cuts63127 : List PrefixCut := [⟨29,89425718,89425772⟩,
⟨64,196429722,196429836⟩]
theorem checked63127 : checkPrefixCuts (2^48) 8278114305 10 Manual.Count131072.C063127.packed 64 cuts63127 = true := by
 decide +kernel
def pointBounds63127 : List (Nat × Nat × Nat) := [(8278173696,114543533830891,114543922597365)]
theorem point_links_checked63127 : (cuts63127.take 1).map (fun c => (8278114305-1+2*2^10*c.k,114543444405173+c.lower,114543833171593+c.upper)) = pointBounds63127 := by
 decide +kernel
def cuts63128 : List PrefixCut := [⟨64,194624522,194624632⟩]
theorem checked63128 : checkPrefixCuts (2^48) 8278245377 10 Manual.Count131072.C063128.packed 64 cuts63128 = true := by
 decide +kernel
def cuts63129 : List PrefixCut := [⟨28,87246827,87246874⟩,
⟨64,195845486,195845592⟩]
theorem checked63129 : checkPrefixCuts (2^48) 8278376449 10 Manual.Count131072.C063129.packed 64 cuts63129 = true := by
 decide +kernel
def pointBounds63129 : List (Nat × Nat × Nat) := [(8278433792,114543922706244,114544311472935)]
theorem point_links_checked63129 : (cuts63129.take 1).map (fun c => (8278376449-1+2*2^10*c.k,114543835459417+c.lower,114544224226061+c.upper)) = pointBounds63129 := by
 decide +kernel
def cuts63130 : List PrefixCut := [⟨64,196352395,196352502⟩]
theorem checked63130 : checkPrefixCuts (2^48) 8278507521 10 Manual.Count131072.C063130.packed 64 cuts63130 = true := by
 decide +kernel
def cuts63131 : List PrefixCut := [⟨27,84014067,84014116⟩,
⟨64,195397280,195397394⟩]
theorem checked63131 : checkPrefixCuts (2^48) 8278638593 10 Manual.Count131072.C063131.packed 64 cuts63131 = true := by
 decide +kernel
def pointBounds63131 : List (Nat × Nat × Nat) := [(8278693888,114544311671365,114544700438271)]
theorem point_links_checked63131 : (cuts63131.take 1).map (fun c => (8278638593-1+2*2^10*c.k,114544227657298+c.lower,114544616424155+c.upper)) = pointBounds63131 := by
 decide +kernel
def cuts63132 : List PrefixCut := [⟨64,193830210,193830320⟩]
theorem checked63132 : checkPrefixCuts (2^48) 8278769665 10 Manual.Count131072.C063132.packed 64 cuts63132 = true := by
 decide +kernel
def cuts63133 : List PrefixCut := [⟨26,79795550,79795597⟩,
⟨64,192671191,192671303⟩]
theorem checked63133 : checkPrefixCuts (2^48) 8278900737 10 Manual.Count131072.C063133.packed 64 cuts63133 = true := by
 decide +kernel
def pointBounds63133 : List (Nat × Nat × Nat) := [(8278953984,114544696680338,114545085447466)]
theorem point_links_checked63133 : (cuts63133.take 1).map (fun c => (8278900737-1+2*2^10*c.k,114544616884788+c.lower,114545005651869+c.upper)) = pointBounds63133 := by
 decide +kernel
def cuts63134 : List PrefixCut := [⟨64,195795971,195796086⟩]
theorem checked63134 : checkPrefixCuts (2^48) 8279031809 10 Manual.Count131072.C063134.packed 64 cuts63134 = true := by
 decide +kernel
def cuts63135 : List PrefixCut := [⟨25,73571418,73571463⟩,
⟨64,195826848,195826964⟩]
theorem checked63135 : checkPrefixCuts (2^48) 8279162881 10 Manual.Count131072.C063135.packed 64 cuts63135 = true := by
 decide +kernel
def pointBounds63135 : List (Nat × Nat × Nat) := [(8279214080,114545078923368,114545467690721)]
theorem point_links_checked63135 : (cuts63135.take 1).map (fun c => (8279162881-1+2*2^10*c.k,114545005351950+c.lower,114545394119258+c.upper)) = pointBounds63135 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000097
