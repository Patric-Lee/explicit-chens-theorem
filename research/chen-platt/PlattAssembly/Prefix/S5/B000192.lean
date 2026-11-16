import PlattAssemblyKernel
import PlattCertificates.Count131072.C046144
import PlattCertificates.Count131072.C046145
import PlattCertificates.Count131072.C046146
import PlattCertificates.Count131072.C046147
import PlattCertificates.Count131072.C046148
import PlattCertificates.Count131072.C046149
import PlattCertificates.Count131072.C046150
import PlattCertificates.Count131072.C046151
import PlattCertificates.Count131072.C046152
import PlattCertificates.Count131072.C046153
import PlattCertificates.Count131072.C046154
import PlattCertificates.Count131072.C046155
import PlattCertificates.Count131072.C046156
import PlattCertificates.Count131072.C046157
import PlattCertificates.Count131072.C046158
import PlattCertificates.Count131072.C046159
import PlattCertificates.Count131072.C046160
import PlattCertificates.Count131072.C046161
import PlattCertificates.Count131072.C046162
import PlattCertificates.Count131072.C046163
import PlattCertificates.Count131072.C046164
import PlattCertificates.Count131072.C046165
import PlattCertificates.Count131072.C046166
import PlattCertificates.Count131072.C046167
import PlattCertificates.Count131072.C046168
import PlattCertificates.Count131072.C046169
import PlattCertificates.Count131072.C046170
import PlattCertificates.Count131072.C046171
import PlattCertificates.Count131072.C046172
import PlattCertificates.Count131072.C046173
import PlattCertificates.Count131072.C046174
import PlattCertificates.Count131072.C046175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46144 : List PrefixCut := [⟨64,269234740,269234896⟩]
theorem checked46144 : checkPrefixCuts (2^48) 6052118529 10 Manual.Count131072.C046144.packed 64 cuts46144 = true := by
 decide +kernel
def cuts46145 : List PrefixCut := [⟨10,42507766,42507793⟩,
⟨64,273554068,273554229⟩]
theorem checked46145 : checkPrefixCuts (2^48) 6052249601 10 Manual.Count131072.C046145.packed 64 cuts46145 = true := by
 decide +kernel
def pointBounds46145 : List (Nat × Nat × Nat) := [(6052270080,110656579639776,110656966189879)]
theorem point_links_checked46145 : (cuts46145.take 1).map (fun c => (6052249601-1+2*2^10*c.k,110656537132010+c.lower,110656923682086+c.upper)) = pointBounds46145 := by
 decide +kernel
def cuts46146 : List PrefixCut := [⟨39,169096439,169096530⟩,
⟨64,273408648,273408798⟩]
theorem checked46146 : checkPrefixCuts (2^48) 6052380673 10 Manual.Count131072.C046146.packed 64 cuts46146 = true := by
 decide +kernel
def pointBounds46146 : List (Nat × Nat × Nat) := [(6052460544,110656979782517,110657366332845)]
theorem point_links_checked46146 : (cuts46146.take 1).map (fun c => (6052380673-1+2*2^10*c.k,110656810686078+c.lower,110657197236315+c.upper)) = pointBounds46146 := by
 decide +kernel
def cuts46147 : List PrefixCut := [⟨64,269682303,269682458⟩]
theorem checked46147 : checkPrefixCuts (2^48) 6052511745 10 Manual.Count131072.C046147.packed 64 cuts46147 = true := by
 decide +kernel
def cuts46148 : List PrefixCut := [⟨4,15671993,15672002⟩,
⟨64,272327160,272327314⟩]
theorem checked46148 : checkPrefixCuts (2^48) 6052642817 10 Manual.Count131072.C046148.packed 64 cuts46148 = true := by
 decide +kernel
def pointBounds46148 : List (Nat × Nat × Nat) := [(6052651008,110657369449022,110657755999573)]
theorem point_links_checked46148 : (cuts46148.take 1).map (fun c => (6052642817-1+2*2^10*c.k,110657353777029+c.lower,110657740327571+c.upper)) = pointBounds46148 := by
 decide +kernel
def cuts46149 : List PrefixCut := [⟨33,140160635,140160715⟩,
⟨64,269531120,269531275⟩]
theorem checked46149 : checkPrefixCuts (2^48) 6052773889 10 Manual.Count131072.C046149.packed 64 cuts46149 = true := by
 decide +kernel
def pointBounds46149 : List (Nat × Nat × Nat) := [(6052841472,110657766264824,110658152815600)]
theorem point_links_checked46149 : (cuts46149.take 1).map (fun c => (6052773889-1+2*2^10*c.k,110657626104189+c.lower,110658012654885+c.upper)) = pointBounds46149 := by
 decide +kernel
def cuts46150 : List PrefixCut := [⟨62,263015080,263015230⟩,
⟨64,272082864,272083020⟩]
theorem checked46150 : checkPrefixCuts (2^48) 6052904961 10 Manual.Count131072.C046150.packed 64 cuts46150 = true := by
 decide +kernel
def pointBounds46150 : List (Nat × Nat × Nat) := [(6053031936,110658158650389,110658545201390)]
theorem point_links_checked46150 : (cuts46150.take 1).map (fun c => (6052904961-1+2*2^10*c.k,110657895635309+c.lower,110658282186160+c.upper)) = pointBounds46150 := by
 decide +kernel
def cuts46151 : List PrefixCut := [⟨64,271797981,271798136⟩]
theorem checked46151 : checkPrefixCuts (2^48) 6053036033 10 Manual.Count131072.C046151.packed 64 cuts46151 = true := by
 decide +kernel
def cuts46152 : List PrefixCut := [⟨27,111833027,111833090⟩,
⟨64,269281064,269281222⟩]
theorem checked46152 : checkPrefixCuts (2^48) 6053167105 10 Manual.Count131072.C046152.packed 64 cuts46152 = true := by
 decide +kernel
def pointBounds46152 : List (Nat × Nat × Nat) := [(6053222400,110658551349181,110658937900406)]
theorem point_links_checked46152 : (cuts46152.take 1).map (fun c => (6053167105-1+2*2^10*c.k,110658439516154+c.lower,110658826067316+c.upper)) = pointBounds46152 := by
 decide +kernel
def cuts46153 : List PrefixCut := [⟨56,237144824,237144956⟩,
⟨64,271135215,271135366⟩]
theorem checked46153 : checkPrefixCuts (2^48) 6053298177 10 Manual.Count131072.C046153.packed 64 cuts46153 = true := by
 decide +kernel
def pointBounds46153 : List (Nat × Nat × Nat) := [(6053412864,110658945942042,110659332493494)]
theorem point_links_checked46153 : (cuts46153.take 1).map (fun c => (6053298177-1+2*2^10*c.k,110658708797218+c.lower,110659095348538+c.upper)) = pointBounds46153 := by
 decide +kernel
def cuts46154 : List PrefixCut := [⟨64,269176448,269176603⟩]
theorem checked46154 : checkPrefixCuts (2^48) 6053429249 10 Manual.Count131072.C046154.packed 64 cuts46154 = true := by
 decide +kernel
def cuts46155 : List PrefixCut := [⟨21,87368333,87368380⟩,
⟨64,266427309,266427462⟩]
theorem checked46155 : checkPrefixCuts (2^48) 6053560321 10 Manual.Count131072.C046155.packed 64 cuts46155 = true := by
 decide +kernel
def pointBounds46155 : List (Nat × Nat × Nat) := [(6053603328,110659336477214,110659723028887)]
theorem point_links_checked46155 : (cuts46155.take 1).map (fun c => (6053560321-1+2*2^10*c.k,110659249108881+c.lower,110659635660507+c.upper)) = pointBounds46155 := by
 decide +kernel
def cuts46156 : List PrefixCut := [⟨50,211184888,211185009⟩,
⟨64,271071106,271071259⟩]
theorem checked46156 : checkPrefixCuts (2^48) 6053691393 10 Manual.Count131072.C046156.packed 64 cuts46156 = true := by
 decide +kernel
def pointBounds46156 : List (Nat × Nat × Nat) := [(6053793792,110659726721078,110660113272978)]
theorem point_links_checked46156 : (cuts46156.take 1).map (fun c => (6053691393-1+2*2^10*c.k,110659515536190+c.lower,110659902087969+c.upper)) = pointBounds46156 := by
 decide +kernel
def cuts46157 : List PrefixCut := [⟨64,269809897,269810054⟩]
theorem checked46157 : checkPrefixCuts (2^48) 6053822465 10 Manual.Count131072.C046157.packed 64 cuts46157 = true := by
 decide +kernel
def cuts46158 : List PrefixCut := [⟨15,65045490,65045528⟩,
⟨64,270640962,270641118⟩]
theorem checked46158 : checkPrefixCuts (2^48) 6053953537 10 Manual.Count131072.C046158.packed 64 cuts46158 = true := by
 decide +kernel
def pointBounds46158 : List (Nat × Nat × Nat) := [(6053984256,110660121462683,110660508014810)]
theorem point_links_checked46158 : (cuts46158.take 1).map (fun c => (6053953537-1+2*2^10*c.k,110660056417193+c.lower,110660442969282+c.upper)) = pointBounds46158 := by
 decide +kernel
def cuts46159 : List PrefixCut := [⟨44,184577373,184577478⟩,
⟨64,268496406,268496558⟩]
theorem checked46159 : checkPrefixCuts (2^48) 6054084609 10 Manual.Count131072.C046159.packed 64 cuts46159 = true := by
 decide +kernel
def pointBounds46159 : List (Nat × Nat × Nat) := [(6054174720,110660511635528,110660898187878)]
theorem point_links_checked46159 : (cuts46159.take 1).map (fun c => (6054084609-1+2*2^10*c.k,110660327058155+c.lower,110660713610400+c.upper)) = pointBounds46159 := by
 decide +kernel
def cuts46160 : List PrefixCut := [⟨64,267467769,267467923⟩]
theorem checked46160 : checkPrefixCuts (2^48) 6054215681 10 Manual.Count131072.C046160.packed 64 cuts46160 = true := by
 decide +kernel
def cuts46161 : List PrefixCut := [⟨9,37564973,37564992⟩,
⟨64,272901405,272901559⟩]
theorem checked46161 : checkPrefixCuts (2^48) 6054346753 10 Manual.Count131072.C046161.packed 64 cuts46161 = true := by
 decide +kernel
def pointBounds46161 : List (Nat × Nat × Nat) := [(6054365184,110660900587303,110661287139873)]
theorem point_links_checked46161 : (cuts46161.take 1).map (fun c => (6054346753-1+2*2^10*c.k,110660863022330+c.lower,110661249574881+c.upper)) = pointBounds46161 := by
 decide +kernel
def cuts46162 : List PrefixCut := [⟨38,160065304,160065395⟩,
⟨64,272709522,272709672⟩]
theorem checked46162 : checkPrefixCuts (2^48) 6054477825 10 Manual.Count131072.C046162.packed 64 cuts46162 = true := by
 decide +kernel
def pointBounds46162 : List (Nat × Nat × Nat) := [(6054555648,110661295989039,110661682541835)]
theorem point_links_checked46162 : (cuts46162.take 1).map (fun c => (6054477825-1+2*2^10*c.k,110661135923735+c.lower,110661522476440+c.upper)) = pointBounds46162 := by
 decide +kernel
def cuts46163 : List PrefixCut := [⟨64,271866824,271866978⟩]
theorem checked46163 : checkPrefixCuts (2^48) 6054608897 10 Manual.Count131072.C046163.packed 64 cuts46163 = true := by
 decide +kernel
def cuts46164 : List PrefixCut := [⟨3,12505361,12505368⟩,
⟨64,268234902,268235057⟩]
theorem checked46164 : checkPrefixCuts (2^48) 6054739969 10 Manual.Count131072.C046164.packed 64 cuts46164 = true := by
 decide +kernel
def pointBounds46164 : List (Nat × Nat × Nat) := [(6054746112,110661693005442,110662079558458)]
theorem point_links_checked46164 : (cuts46164.take 1).map (fun c => (6054739969-1+2*2^10*c.k,110661680500081+c.lower,110662067053090+c.upper)) = pointBounds46164 := by
 decide +kernel
def cuts46165 : List PrefixCut := [⟨32,136718532,136718612⟩,
⟨64,271297228,271297384⟩]
theorem checked46165 : checkPrefixCuts (2^48) 6054871041 10 Manual.Count131072.C046165.packed 64 cuts46165 = true := by
 decide +kernel
def pointBounds46165 : List (Nat × Nat × Nat) := [(6054936576,110662085453515,110662472006759)]
theorem point_links_checked46165 : (cuts46165.take 1).map (fun c => (6054871041-1+2*2^10*c.k,110661948734983+c.lower,110662335288147+c.upper)) = pointBounds46165 := by
 decide +kernel
def cuts46166 : List PrefixCut := [⟨61,261250548,261250698⟩,
⟨64,273569168,273569326⟩]
theorem checked46166 : checkPrefixCuts (2^48) 6055002113 10 Manual.Count131072.C046166.packed 64 cuts46166 = true := by
 decide +kernel
def pointBounds46166 : List (Nat × Nat × Nat) := [(6055127040,110662481282759,110662867836229)]
theorem point_links_checked46166 : (cuts46166.take 1).map (fun c => (6055002113-1+2*2^10*c.k,110662220032211+c.lower,110662606585531+c.upper)) = pointBounds46166 := by
 decide +kernel
def cuts46167 : List PrefixCut := [⟨64,273470260,273470424⟩]
theorem checked46167 : checkPrefixCuts (2^48) 6055133185 10 Manual.Count131072.C046167.packed 64 cuts46167 = true := by
 decide +kernel
def cuts46168 : List PrefixCut := [⟨26,107285357,107285416⟩,
⟨64,266352306,266352458⟩]
theorem checked46168 : checkPrefixCuts (2^48) 6055264257 10 Manual.Count131072.C046168.packed 64 cuts46168 = true := by
 decide +kernel
def pointBounds46168 : List (Nat × Nat × Nat) := [(6055317504,110662874356996,110663260910697)]
theorem point_links_checked46168 : (cuts46168.take 1).map (fun c => (6055264257-1+2*2^10*c.k,110662767071639+c.lower,110663153625281+c.upper)) = pointBounds46168 := by
 decide +kernel
def cuts46169 : List PrefixCut := [⟨55,231019956,231020088⟩,
⟨64,268949584,268949737⟩]
theorem checked46169 : checkPrefixCuts (2^48) 6055395329 10 Manual.Count131072.C046169.packed 64 cuts46169 = true := by
 decide +kernel
def pointBounds46169 : List (Nat × Nat × Nat) := [(6055507968,110663264443901,110663650997827)]
theorem point_links_checked46169 : (cuts46169.take 1).map (fun c => (6055395329-1+2*2^10*c.k,110663033423945+c.lower,110663419977739+c.upper)) = pointBounds46169 := by
 decide +kernel
def cuts46170 : List PrefixCut := [⟨64,266852098,266852256⟩]
theorem checked46170 : checkPrefixCuts (2^48) 6055526401 10 Manual.Count131072.C046170.packed 64 cuts46170 = true := by
 decide +kernel
def cuts46171 : List PrefixCut := [⟨20,84781625,84781675⟩,
⟨64,270657753,270657905⟩]
theorem checked46171 : checkPrefixCuts (2^48) 6055657473 10 Manual.Count131072.C046171.packed 64 cuts46171 = true := by
 decide +kernel
def pointBounds46171 : List (Nat × Nat × Nat) := [(6055698432,110663654007252,110664040561407)]
theorem point_links_checked46171 : (cuts46171.take 1).map (fun c => (6055657473-1+2*2^10*c.k,110663569225627+c.lower,110663955779732+c.upper)) = pointBounds46171 := by
 decide +kernel
def cuts46172 : List PrefixCut := [⟨49,209717390,209717506⟩,
⟨64,274742093,274742249⟩]
theorem checked46172 : checkPrefixCuts (2^48) 6055788545 10 Manual.Count131072.C046172.packed 64 cuts46172 = true := by
 decide +kernel
def pointBounds46172 : List (Nat × Nat × Nat) := [(6055888896,110664049600770,110664436155143)]
theorem point_links_checked46172 : (cuts46172.take 1).map (fun c => (6055788545-1+2*2^10*c.k,110663839883380+c.lower,110664226437637+c.upper)) = pointBounds46172 := by
 decide +kernel
def cuts46173 : List PrefixCut := [⟨64,269716434,269716588⟩]
theorem checked46173 : checkPrefixCuts (2^48) 6055919617 10 Manual.Count131072.C046173.packed 64 cuts46173 = true := by
 decide +kernel
def cuts46174 : List PrefixCut := [⟨14,59120246,59120281⟩,
⟨64,269896537,269896693⟩]
theorem checked46174 : checkPrefixCuts (2^48) 6056050689 10 Manual.Count131072.C046174.packed 64 cuts46174 = true := by
 decide +kernel
def pointBounds46174 : List (Nat × Nat × Nat) := [(6056079360,110664443462153,110664830016755)]
theorem point_links_checked46174 : (cuts46174.take 1).map (fun c => (6056050689-1+2*2^10*c.k,110664384341907+c.lower,110664770896474+c.upper)) = pointBounds46174 := by
 decide +kernel
def cuts46175 : List PrefixCut := [⟨43,180377037,180377137⟩,
⟨64,266776750,266776896⟩]
theorem checked46175 : checkPrefixCuts (2^48) 6056181761 10 Manual.Count131072.C046175.packed 64 cuts46175 = true := by
 decide +kernel
def pointBounds46175 : List (Nat × Nat × Nat) := [(6056269824,110664834615481,110665221170304)]
theorem point_links_checked46175 : (cuts46175.take 1).map (fun c => (6056181761-1+2*2^10*c.k,110664654238444+c.lower,110665040793167+c.upper)) = pointBounds46175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000192
