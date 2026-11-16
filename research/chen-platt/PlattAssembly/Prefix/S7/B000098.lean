import PlattAssemblyKernel
import PlattCertificates.Count131072.C063136
import PlattCertificates.Count131072.C063137
import PlattCertificates.Count131072.C063138
import PlattCertificates.Count131072.C063139
import PlattCertificates.Count131072.C063140
import PlattCertificates.Count131072.C063141
import PlattCertificates.Count131072.C063142
import PlattCertificates.Count131072.C063143
import PlattCertificates.Count131072.C063144
import PlattCertificates.Count131072.C063145
import PlattCertificates.Count131072.C063146
import PlattCertificates.Count131072.C063147
import PlattCertificates.Count131072.C063148
import PlattCertificates.Count131072.C063149
import PlattCertificates.Count131072.C063150
import PlattCertificates.Count131072.C063151
import PlattCertificates.Count131072.C063152
import PlattCertificates.Count131072.C063153
import PlattCertificates.Count131072.C063154
import PlattCertificates.Count131072.C063155
import PlattCertificates.Count131072.C063156
import PlattCertificates.Count131072.C063157
import PlattCertificates.Count131072.C063158
import PlattCertificates.Count131072.C063159
import PlattCertificates.Count131072.C063160
import PlattCertificates.Count131072.C063161
import PlattCertificates.Count131072.C063162
import PlattCertificates.Count131072.C063163
import PlattCertificates.Count131072.C063164
import PlattCertificates.Count131072.C063165
import PlattCertificates.Count131072.C063166
import PlattCertificates.Count131072.C063167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63136 : List PrefixCut := [⟨64,198033588,198033699⟩]
theorem checked63136 : checkPrefixCuts (2^48) 8279293953 10 Manual.Count131072.C063136.packed 64 cuts63136 = true := by
 decide +kernel
def cuts63137 : List PrefixCut := [⟨24,73467113,73467155⟩,
⟨64,198200433,198200544⟩]
theorem checked63137 : checkPrefixCuts (2^48) 8279425025 10 Manual.Count131072.C063137.packed 64 cuts63137 = true := by
 decide +kernel
def pointBounds63137 : List (Nat × Nat × Nat) := [(8279474176,114545472679499,114545861447076)]
theorem point_links_checked63137 : (cuts63137.take 1).map (fun c => (8279425025-1+2*2^10*c.k,114545399212386+c.lower,114545787979921+c.upper)) = pointBounds63137 := by
 decide +kernel
def cuts63138 : List PrefixCut := [⟨64,197143417,197143526⟩]
theorem checked63138 : checkPrefixCuts (2^48) 8279556097 10 Manual.Count131072.C063138.packed 64 cuts63138 = true := by
 decide +kernel
def cuts63139 : List PrefixCut := [⟨23,69861245,69861285⟩,
⟨64,193536766,193536880⟩]
theorem checked63139 : checkPrefixCuts (2^48) 8279687169 10 Manual.Count131072.C063139.packed 64 cuts63139 = true := by
 decide +kernel
def pointBounds63139 : List (Nat × Nat × Nat) := [(8279734272,114545864417481,114546253185276)]
theorem point_links_checked63139 : (cuts63139.take 1).map (fun c => (8279687169-1+2*2^10*c.k,114545794556236+c.lower,114546183323991+c.upper)) = pointBounds63139 := by
 decide +kernel
def cuts63140 : List PrefixCut := [⟨64,193499707,193499822⟩]
theorem checked63140 : checkPrefixCuts (2^48) 8279818241 10 Manual.Count131072.C063140.packed 64 cuts63140 = true := by
 decide +kernel
def cuts63141 : List PrefixCut := [⟨22,64827833,64827875⟩,
⟨64,197609961,197610078⟩]
theorem checked63141 : checkPrefixCuts (2^48) 8279949313 10 Manual.Count131072.C063141.packed 64 cuts63141 = true := by
 decide +kernel
def pointBounds63141 : List (Nat × Nat × Nat) := [(8279994368,114546246420542,114546635188568)]
theorem point_links_checked63141 : (cuts63141.take 1).map (fun c => (8279949313-1+2*2^10*c.k,114546181592709+c.lower,114546570360693+c.upper)) = pointBounds63141 := by
 decide +kernel
def cuts63142 : List PrefixCut := [⟨64,195499235,195499349⟩]
theorem checked63142 : checkPrefixCuts (2^48) 8280080385 10 Manual.Count131072.C063142.packed 64 cuts63142 = true := by
 decide +kernel
def cuts63143 : List PrefixCut := [⟨21,64009941,64009980⟩,
⟨64,192028796,192028912⟩]
theorem checked63143 : checkPrefixCuts (2^48) 8280211457 10 Manual.Count131072.C063143.packed 64 cuts63143 = true := by
 decide +kernel
def pointBounds63143 : List (Nat × Nat × Nat) := [(8280254464,114546638711846,114547027480100)]
theorem point_links_checked63143 : (cuts63143.take 1).map (fun c => (8280211457-1+2*2^10*c.k,114546574701905+c.lower,114546963470120+c.upper)) = pointBounds63143 := by
 decide +kernel
def cuts63144 : List PrefixCut := [⟨64,197158683,197158792⟩]
theorem checked63144 : checkPrefixCuts (2^48) 8280342529 10 Manual.Count131072.C063144.packed 64 cuts63144 = true := by
 decide +kernel
def cuts63145 : List PrefixCut := [⟨20,62206319,62206354⟩,
⟨64,196985609,196985721⟩]
theorem checked63145 : checkPrefixCuts (2^48) 8280473601 10 Manual.Count131072.C063145.packed 64 cuts63145 = true := by
 decide +kernel
def pointBounds63145 : List (Nat × Nat × Nat) := [(8280514560,114547026095703,114547414864178)]
theorem point_links_checked63145 : (cuts63145.take 1).map (fun c => (8280473601-1+2*2^10*c.k,114546963889384+c.lower,114547352657824+c.upper)) = pointBounds63145 := by
 decide +kernel
def cuts63146 : List PrefixCut := [⟨64,195248884,195248999⟩]
theorem checked63146 : checkPrefixCuts (2^48) 8280604673 10 Manual.Count131072.C063146.packed 64 cuts63146 = true := by
 decide +kernel
def cuts63147 : List PrefixCut := [⟨19,58703237,58703269⟩,
⟨64,196639457,196639571⟩]
theorem checked63147 : checkPrefixCuts (2^48) 8280735745 10 Manual.Count131072.C063147.packed 64 cuts63147 = true := by
 decide +kernel
def pointBounds63147 : List (Nat × Nat × Nat) := [(8280774656,114547414827114,114547803595813)]
theorem point_links_checked63147 : (cuts63147.take 1).map (fun c => (8280735745-1+2*2^10*c.k,114547356123877+c.lower,114547744892544+c.upper)) = pointBounds63147 := by
 decide +kernel
def cuts63148 : List PrefixCut := [⟨64,195888552,195888667⟩]
theorem checked63148 : checkPrefixCuts (2^48) 8280866817 10 Manual.Count131072.C063148.packed 64 cuts63148 = true := by
 decide +kernel
def cuts63149 : List PrefixCut := [⟨18,53432880,53432911⟩,
⟨64,192486428,192486538⟩]
theorem checked63149 : checkPrefixCuts (2^48) 8280997889 10 Manual.Count131072.C063149.packed 64 cuts63149 = true := by
 decide +kernel
def pointBounds63149 : List (Nat × Nat × Nat) := [(8281034752,114547802084766,114548190853693)]
theorem point_links_checked63149 : (cuts63149.take 1).map (fun c => (8280997889-1+2*2^10*c.k,114547748651886+c.lower,114548137420782+c.upper)) = pointBounds63149 := by
 decide +kernel
def cuts63150 : List PrefixCut := [⟨64,193639038,193639150⟩]
theorem checked63150 : checkPrefixCuts (2^48) 8281128961 10 Manual.Count131072.C063150.packed 64 cuts63150 = true := by
 decide +kernel
def cuts63151 : List PrefixCut := [⟨17,51561782,51561812⟩,
⟨64,193533986,193534098⟩]
theorem checked63151 : checkPrefixCuts (2^48) 8281260033 10 Manual.Count131072.C063151.packed 64 cuts63151 = true := by
 decide +kernel
def pointBounds63151 : List (Nat × Nat × Nat) := [(8281294848,114548186339134,114548575108282)]
theorem point_links_checked63151 : (cuts63151.take 1).map (fun c => (8281260033-1+2*2^10*c.k,114548134777352+c.lower,114548523546470+c.upper)) = pointBounds63151 := by
 decide +kernel
def cuts63152 : List PrefixCut := [⟨64,196284019,196284130⟩]
theorem checked63152 : checkPrefixCuts (2^48) 8281391105 10 Manual.Count131072.C063152.packed 64 cuts63152 = true := by
 decide +kernel
def cuts63153 : List PrefixCut := [⟨16,47413593,47413617⟩,
⟨64,191862463,191862567⟩]
theorem checked63153 : checkPrefixCuts (2^48) 8281522177 10 Manual.Count131072.C063153.packed 64 cuts63153 = true := by
 decide +kernel
def pointBounds63153 : List (Nat × Nat × Nat) := [(8281554944,114548572008950,114548960778315)]
theorem point_links_checked63153 : (cuts63153.take 1).map (fun c => (8281522177-1+2*2^10*c.k,114548524595357+c.lower,114548913364698+c.upper)) = pointBounds63153 := by
 decide +kernel
def cuts63154 : List PrefixCut := [⟨64,192811075,192811190⟩]
theorem checked63154 : checkPrefixCuts (2^48) 8281653249 10 Manual.Count131072.C063154.packed 64 cuts63154 = true := by
 decide +kernel
def cuts63155 : List PrefixCut := [⟨15,44897043,44897072⟩,
⟨64,196070756,196070866⟩]
theorem checked63155 : checkPrefixCuts (2^48) 8281784321 10 Manual.Count131072.C063155.packed 64 cuts63155 = true := by
 decide +kernel
def pointBounds63155 : List (Nat × Nat × Nat) := [(8281815040,114548954165938,114549342935527)]
theorem point_links_checked63155 : (cuts63155.take 1).map (fun c => (8281784321-1+2*2^10*c.k,114548909268895+c.lower,114549298038455+c.upper)) = pointBounds63155 := by
 decide +kernel
def cuts63156 : List PrefixCut := [⟨64,196713399,196713509⟩]
theorem checked63156 : checkPrefixCuts (2^48) 8281915393 10 Manual.Count131072.C063156.packed 64 cuts63156 = true := by
 decide +kernel
def cuts63157 : List PrefixCut := [⟨14,41904853,41904878⟩,
⟨64,193583589,193583701⟩]
theorem checked63157 : checkPrefixCuts (2^48) 8282046465 10 Manual.Count131072.C063157.packed 64 cuts63157 = true := by
 decide +kernel
def pointBounds63157 : List (Nat × Nat × Nat) := [(8282075136,114549343957903,114549732727708)]
theorem point_links_checked63157 : (cuts63157.take 1).map (fun c => (8282046465-1+2*2^10*c.k,114549302053050+c.lower,114549690822830+c.upper)) = pointBounds63157 := by
 decide +kernel
def cuts63158 : List PrefixCut := [⟨64,195449736,195449847⟩]
theorem checked63158 : checkPrefixCuts (2^48) 8282177537 10 Manual.Count131072.C063158.packed 64 cuts63158 = true := by
 decide +kernel
def cuts63159 : List PrefixCut := [⟨13,39728492,39728514⟩,
⟨64,193951323,193951434⟩]
theorem checked63159 : checkPrefixCuts (2^48) 8282308609 10 Manual.Count131072.C063159.packed 64 cuts63159 = true := by
 decide +kernel
def pointBounds63159 : List (Nat × Nat × Nat) := [(8282335232,114549730814867,114550119584892)]
theorem point_links_checked63159 : (cuts63159.take 1).map (fun c => (8282308609-1+2*2^10*c.k,114549691086375+c.lower,114550079856378+c.upper)) = pointBounds63159 := by
 decide +kernel
def cuts63160 : List PrefixCut := [⟨64,195273626,195273740⟩]
theorem checked63160 : checkPrefixCuts (2^48) 8282439681 10 Manual.Count131072.C063160.packed 64 cuts63160 = true := by
 decide +kernel
def cuts63161 : List PrefixCut := [⟨12,36464781,36464800⟩,
⟨64,196493945,196494055⟩]
theorem checked63161 : checkPrefixCuts (2^48) 8282570753 10 Manual.Count131072.C063161.packed 64 cuts63161 = true := by
 decide +kernel
def pointBounds63161 : List (Nat × Nat × Nat) := [(8282595328,114550116776105,114550505546352)]
theorem point_links_checked63161 : (cuts63161.take 1).map (fun c => (8282570753-1+2*2^10*c.k,114550080311324+c.lower,114550469081552+c.upper)) = pointBounds63161 := by
 decide +kernel
def cuts63162 : List PrefixCut := [⟨64,193976074,193976191⟩]
theorem checked63162 : checkPrefixCuts (2^48) 8282701825 10 Manual.Count131072.C063162.packed 64 cuts63162 = true := by
 decide +kernel
def cuts63163 : List PrefixCut := [⟨11,32861444,32861463⟩,
⟨64,195604164,195604281⟩]
theorem checked63163 : checkPrefixCuts (2^48) 8282832897 10 Manual.Count131072.C063163.packed 64 cuts63163 = true := by
 decide +kernel
def pointBounds63163 : List (Nat × Nat × Nat) := [(8282855424,114550503642787,114550892413261)]
theorem point_links_checked63163 : (cuts63163.take 1).map (fun c => (8282832897-1+2*2^10*c.k,114550470781343+c.lower,114550859551798+c.upper)) = pointBounds63163 := by
 decide +kernel
def cuts63164 : List PrefixCut := [⟨64,194683550,194683665⟩]
theorem checked63164 : checkPrefixCuts (2^48) 8282963969 10 Manual.Count131072.C063164.packed 64 cuts63164 = true := by
 decide +kernel
def cuts63165 : List PrefixCut := [⟨10,30039917,30039936⟩,
⟨64,195326118,195326235⟩]
theorem checked63165 : checkPrefixCuts (2^48) 8283095041 10 Manual.Count131072.C063165.packed 64 cuts63165 = true := by
 decide +kernel
def pointBounds63165 : List (Nat × Nat × Nat) := [(8283115520,114550891108974,114551279879680)]
theorem point_links_checked63165 : (cuts63165.take 1).map (fun c => (8283095041-1+2*2^10*c.k,114550861069057+c.lower,114551249839744+c.upper)) = pointBounds63165 := by
 decide +kernel
def cuts63166 : List PrefixCut := [⟨64,197599772,197599884⟩]
theorem checked63166 : checkPrefixCuts (2^48) 8283226113 10 Manual.Count131072.C063166.packed 64 cuts63166 = true := by
 decide +kernel
def cuts63167 : List PrefixCut := [⟨9,28475858,28475874⟩,
⟨64,194640358,194640473⟩]
theorem checked63167 : checkPrefixCuts (2^48) 8283357185 10 Manual.Count131072.C063167.packed 64 cuts63167 = true := by
 decide +kernel
def pointBounds63167 : List (Nat × Nat × Nat) := [(8283375616,114551282470805,114551671241737)]
theorem point_links_checked63167 : (cuts63167.take 1).map (fun c => (8283357185-1+2*2^10*c.k,114551253994947+c.lower,114551642765863+c.upper)) = pointBounds63167 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000098
