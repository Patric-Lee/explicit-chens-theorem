import PlattAssemblyKernel
import PlattCertificates.Count131072.C054992
import PlattCertificates.Count131072.C054993
import PlattCertificates.Count131072.C054994
import PlattCertificates.Count131072.C054995
import PlattCertificates.Count131072.C054996
import PlattCertificates.Count131072.C054997
import PlattCertificates.Count131072.C054998
import PlattCertificates.Count131072.C054999
import PlattCertificates.Count131072.C055000
import PlattCertificates.Count131072.C055001
import PlattCertificates.Count131072.C055002
import PlattCertificates.Count131072.C055003
import PlattCertificates.Count131072.C055004
import PlattCertificates.Count131072.C055005
import PlattCertificates.Count131072.C055006
import PlattCertificates.Count131072.C055007
import PlattCertificates.Count131072.C055008
import PlattCertificates.Count131072.C055009
import PlattCertificates.Count131072.C055010
import PlattCertificates.Count131072.C055011
import PlattCertificates.Count131072.C055012
import PlattCertificates.Count131072.C055013
import PlattCertificates.Count131072.C055014
import PlattCertificates.Count131072.C055015
import PlattCertificates.Count131072.C055016
import PlattCertificates.Count131072.C055017
import PlattCertificates.Count131072.C055018
import PlattCertificates.Count131072.C055019
import PlattCertificates.Count131072.C055020
import PlattCertificates.Count131072.C055021
import PlattCertificates.Count131072.C055022
import PlattCertificates.Count131072.C055023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54992 : List PrefixCut := [⟨64,225120314,225120443⟩]
theorem checked54992 : checkPrefixCuts (2^48) 7211843585 10 Manual.Count131072.C054992.packed 64 cuts54992 = true := by
 decide +kernel
def cuts54993 : List PrefixCut := [⟨44,153304263,153304352⟩,
⟨64,224179521,224179650⟩]
theorem checked54993 : checkPrefixCuts (2^48) 7211974657 10 Manual.Count131072.C054993.packed 64 cuts54993 = true := by
 decide +kernel
def pointBounds54993 : List (Nat × Nat × Nat) := [(7212064768,112839081110167,112839468903969)]
theorem point_links_checked54993 : (cuts54993.take 1).map (fun c => (7211974657-1+2*2^10*c.k,112838927805904+c.lower,112839315599617+c.upper)) = pointBounds54993 := by
 decide +kernel
def cuts54994 : List PrefixCut := [⟨64,223394910,223395037⟩]
theorem checked54994 : checkPrefixCuts (2^48) 7212105729 10 Manual.Count131072.C054994.packed 64 cuts54994 = true := by
 decide +kernel
def cuts54995 : List PrefixCut := [⟨27,94836235,94836288⟩,
⟨64,227683801,227683929⟩]
theorem checked54995 : checkPrefixCuts (2^48) 7212236801 10 Manual.Count131072.C054995.packed 64 cuts54995 = true := by
 decide +kernel
def pointBounds54995 : List (Nat × Nat × Nat) := [(7212292096,112839470216570,112839858010592)]
theorem point_links_checked54995 : (cuts54995.take 1).map (fun c => (7212236801-1+2*2^10*c.k,112839375380335+c.lower,112839763174304+c.upper)) = pointBounds54995 := by
 decide +kernel
def cuts54996 : List PrefixCut := [⟨64,225572247,225572377⟩]
theorem checked54996 : checkPrefixCuts (2^48) 7212367873 10 Manual.Count131072.C054996.packed 64 cuts54996 = true := by
 decide +kernel
def cuts54997 : List PrefixCut := [⟨10,35123339,35123357⟩,
⟨64,227441381,227441507⟩]
theorem checked54997 : checkPrefixCuts (2^48) 7212498945 10 Manual.Count131072.C054997.packed 64 cuts54997 = true := by
 decide +kernel
def pointBounds54997 : List (Nat × Nat × Nat) := [(7212519424,112839863759722,112840251553967)]
theorem point_links_checked54997 : (cuts54997.take 1).map (fun c => (7212498945-1+2*2^10*c.k,112839828636383+c.lower,112840216430610+c.upper)) = pointBounds54997 := by
 decide +kernel
def cuts54998 : List PrefixCut := [⟨57,200666368,200666481⟩,
⟨64,224900649,224900775⟩]
theorem checked54998 : checkPrefixCuts (2^48) 7212630017 10 Manual.Count131072.C054998.packed 64 cuts54998 = true := by
 decide +kernel
def pointBounds54998 : List (Nat × Nat × Nat) := [(7212746752,112840256744132,112840644538598)]
theorem point_links_checked54998 : (cuts54998.take 1).map (fun c => (7212630017-1+2*2^10*c.k,112840056077764+c.lower,112840443872117+c.upper)) = pointBounds54998 := by
 decide +kernel
def cuts54999 : List PrefixCut := [⟨64,224974566,224974696⟩]
theorem checked54999 : checkPrefixCuts (2^48) 7212761089 10 Manual.Count131072.C054999.packed 64 cuts54999 = true := by
 decide +kernel
def cuts55000 : List PrefixCut := [⟨40,138924143,138924220⟩,
⟨64,222551039,222551165⟩]
theorem checked55000 : checkPrefixCuts (2^48) 7212892161 10 Manual.Count131072.C055000.packed 64 cuts55000 = true := by
 decide +kernel
def pointBounds55000 : List (Nat × Nat × Nat) := [(7212974080,112840644877122,112841032671808)]
theorem point_links_checked55000 : (cuts55000.take 1).map (fun c => (7212892161-1+2*2^10*c.k,112840505952979+c.lower,112840893747588+c.upper)) = pointBounds55000 := by
 decide +kernel
def cuts55001 : List PrefixCut := [⟨64,222117785,222117911⟩]
theorem checked55001 : checkPrefixCuts (2^48) 7213023233 10 Manual.Count131072.C055001.packed 64 cuts55001 = true := by
 decide +kernel
def cuts55002 : List PrefixCut := [⟨23,81322510,81322556⟩,
⟨64,225547674,225547803⟩]
theorem checked55002 : checkPrefixCuts (2^48) 7213154305 10 Manual.Count131072.C055002.packed 64 cuts55002 = true := by
 decide +kernel
def pointBounds55002 : List (Nat × Nat × Nat) := [(7213201408,112841031944313,112841419739220)]
theorem point_links_checked55002 : (cuts55002.take 1).map (fun c => (7213154305-1+2*2^10*c.k,112840950621803+c.lower,112841338416664+c.upper)) = pointBounds55002 := by
 decide +kernel
def cuts55003 : List PrefixCut := [⟨64,227455629,227455756⟩]
theorem checked55003 : checkPrefixCuts (2^48) 7213285377 10 Manual.Count131072.C055003.packed 64 cuts55003 = true := by
 decide +kernel
def cuts55004 : List PrefixCut := [⟨6,20915253,20915265⟩,
⟨64,228583068,228583200⟩]
theorem checked55004 : checkPrefixCuts (2^48) 7213416449 10 Manual.Count131072.C055004.packed 64 cuts55004 = true := by
 decide +kernel
def pointBounds55004 : List (Nat × Nat × Nat) := [(7213428736,112841424540359,112841812335488)]
theorem point_links_checked55004 : (cuts55004.take 1).map (fun c => (7213416449-1+2*2^10*c.k,112841403625106+c.lower,112841791420223+c.upper)) = pointBounds55004 := by
 decide +kernel
def cuts55005 : List PrefixCut := [⟨53,187061984,187062092⟩,
⟨64,226862044,226862174⟩]
theorem checked55005 : checkPrefixCuts (2^48) 7213547521 10 Manual.Count131072.C055005.packed 64 cuts55005 = true := by
 decide +kernel
def pointBounds55005 : List (Nat × Nat × Nat) := [(7213656064,112841819270158,112842207065515)]
theorem point_links_checked55005 : (cuts55005.take 1).map (fun c => (7213547521-1+2*2^10*c.k,112841632208174+c.lower,112842020003423+c.upper)) = pointBounds55005 := by
 decide +kernel
def cuts55006 : List PrefixCut := [⟨64,224750878,224751007⟩]
theorem checked55006 : checkPrefixCuts (2^48) 7213678593 10 Manual.Count131072.C055006.packed 64 cuts55006 = true := by
 decide +kernel
def cuts55007 : List PrefixCut := [⟨36,126147446,126147517⟩,
⟨64,224395630,224395757⟩]
theorem checked55007 : checkPrefixCuts (2^48) 7213809665 10 Manual.Count131072.C055007.packed 64 cuts55007 = true := by
 decide +kernel
def pointBounds55007 : List (Nat × Nat × Nat) := [(7213883392,112842209968542,112842597764121)]
theorem point_links_checked55007 : (cuts55007.take 1).map (fun c => (7213809665-1+2*2^10*c.k,112842083821096+c.lower,112842471616604+c.upper)) = pointBounds55007 := by
 decide +kernel
def cuts55008 : List PrefixCut := [⟨64,220684884,220685011⟩]
theorem checked55008 : checkPrefixCuts (2^48) 7213940737 10 Manual.Count131072.C055008.packed 64 cuts55008 = true := by
 decide +kernel
def cuts55009 : List PrefixCut := [⟨19,68631563,68631600⟩,
⟨64,227508872,227508997⟩]
theorem checked55009 : checkPrefixCuts (2^48) 7214071809 10 Manual.Count131072.C055009.packed 64 cuts55009 = true := by
 decide +kernel
def pointBounds55009 : List (Nat × Nat × Nat) := [(7214110720,112842597533173,112842985328972)]
theorem point_links_checked55009 : (cuts55009.take 1).map (fun c => (7214071809-1+2*2^10*c.k,112842528901610+c.lower,112842916697372+c.upper)) = pointBounds55009 := by
 decide +kernel
def cuts55010 : List PrefixCut := [⟨64,222705682,222705810⟩]
theorem checked55010 : checkPrefixCuts (2^48) 7214202881 10 Manual.Count131072.C055010.packed 64 cuts55010 = true := by
 decide +kernel
def cuts55011 : List PrefixCut := [⟨2,6710760,6710764⟩,
⟨64,224730481,224730608⟩]
theorem checked55011 : checkPrefixCuts (2^48) 7214333953 10 Manual.Count131072.C055011.packed 64 cuts55011 = true := by
 decide +kernel
def pointBounds55011 : List (Nat × Nat × Nat) := [(7214338048,112842985826924,112843373622943)]
theorem point_links_checked55011 : (cuts55011.take 1).map (fun c => (7214333953-1+2*2^10*c.k,112842979116164+c.lower,112843366912179+c.upper)) = pointBounds55011 := by
 decide +kernel
def cuts55012 : List PrefixCut := [⟨49,172134539,172134635⟩,
⟨64,224921464,224921590⟩]
theorem checked55012 : checkPrefixCuts (2^48) 7214465025 10 Manual.Count131072.C055012.packed 64 cuts55012 = true := by
 decide +kernel
def pointBounds55012 : List (Nat × Nat × Nat) := [(7214565376,112843375981184,112843763777422)]
theorem point_links_checked55012 : (cuts55012.take 1).map (fun c => (7214465025-1+2*2^10*c.k,112843203846645+c.lower,112843591642787+c.upper)) = pointBounds55012 := by
 decide +kernel
def cuts55013 : List PrefixCut := [⟨64,222537496,222537624⟩]
theorem checked55013 : checkPrefixCuts (2^48) 7214596097 10 Manual.Count131072.C055013.packed 64 cuts55013 = true := by
 decide +kernel
def cuts55014 : List PrefixCut := [⟨32,110682032,110682097⟩,
⟨64,223352740,223352869⟩]
theorem checked55014 : checkPrefixCuts (2^48) 7214727169 10 Manual.Count131072.C055014.packed 64 cuts55014 = true := by
 decide +kernel
def pointBounds55014 : List (Nat × Nat × Nat) := [(7214792704,112843761987637,112844149784098)]
theorem point_links_checked55014 : (cuts55014.take 1).map (fun c => (7214727169-1+2*2^10*c.k,112843651305605+c.lower,112844039102001+c.upper)) = pointBounds55014 := by
 decide +kernel
def cuts55015 : List PrefixCut := [⟨64,224011934,224012061⟩]
theorem checked55015 : checkPrefixCuts (2^48) 7214858241 10 Manual.Count131072.C055015.packed 64 cuts55015 = true := by
 decide +kernel
def cuts55016 : List PrefixCut := [⟨15,51652465,51652495⟩,
⟨64,224866102,224866233⟩]
theorem checked55016 : checkPrefixCuts (2^48) 7214989313 10 Manual.Count131072.C055016.packed 64 cuts55016 = true := by
 decide +kernel
def pointBounds55016 : List (Nat × Nat × Nat) := [(7215020032,112844150322744,112844538119426)]
theorem point_links_checked55016 : (cuts55016.take 1).map (fun c => (7214989313-1+2*2^10*c.k,112844098670279+c.lower,112844486466931+c.upper)) = pointBounds55016 := by
 decide +kernel
def cuts55017 : List PrefixCut := [⟨62,217605951,217606077⟩,
⟨64,223574651,223574781⟩]
theorem checked55017 : checkPrefixCuts (2^48) 7215120385 10 Manual.Count131072.C055017.packed 64 cuts55017 = true := by
 decide +kernel
def pointBounds55017 : List (Nat × Nat × Nat) := [(7215247360,112844541142332,112844928939241)]
theorem point_links_checked55017 : (cuts55017.take 1).map (fun c => (7215120385-1+2*2^10*c.k,112844323536381+c.lower,112844711333164+c.upper)) = pointBounds55017 := by
 decide +kernel
def cuts55018 : List PrefixCut := [⟨64,225052998,225053126⟩]
theorem checked55018 : checkPrefixCuts (2^48) 7215251457 10 Manual.Count131072.C055018.packed 64 cuts55018 = true := by
 decide +kernel
def cuts55019 : List PrefixCut := [⟨45,157327889,157327981⟩,
⟨64,221967111,221967239⟩]
theorem checked55019 : checkPrefixCuts (2^48) 7215382529 10 Manual.Count131072.C055019.packed 64 cuts55019 = true := by
 decide +kernel
def pointBounds55019 : List (Nat × Nat × Nat) := [(7215474688,112844929491919,112845317289052)]
theorem point_links_checked55019 : (cuts55019.take 1).map (fun c => (7215382529-1+2*2^10*c.k,112844772164030+c.lower,112845159961071+c.upper)) = pointBounds55019 := by
 decide +kernel
def cuts55020 : List PrefixCut := [⟨64,225551952,225552078⟩]
theorem checked55020 : checkPrefixCuts (2^48) 7215513601 10 Manual.Count131072.C055020.packed 64 cuts55020 = true := by
 decide +kernel
def cuts55021 : List PrefixCut := [⟨28,97327003,97327057⟩,
⟨64,224806667,224806793⟩]
theorem checked55021 : checkPrefixCuts (2^48) 7215644673 10 Manual.Count131072.C055021.packed 64 cuts55021 = true := by
 decide +kernel
def pointBounds55021 : List (Nat × Nat × Nat) := [(7215702016,112845317010096,112845704807445)]
theorem point_links_checked55021 : (cuts55021.take 1).map (fun c => (7215644673-1+2*2^10*c.k,112845219683093+c.lower,112845607480388+c.upper)) = pointBounds55021 := by
 decide +kernel
def cuts55022 : List PrefixCut := [⟨64,226050854,226050983⟩]
theorem checked55022 : checkPrefixCuts (2^48) 7215775745 10 Manual.Count131072.C055022.packed 64 cuts55022 = true := by
 decide +kernel
def cuts55023 : List PrefixCut := [⟨11,38344370,38344392⟩,
⟨64,226319793,226319920⟩]
theorem checked55023 : checkPrefixCuts (2^48) 7215906817 10 Manual.Count131072.C055023.packed 64 cuts55023 = true := by
 decide +kernel
def pointBounds55023 : List (Nat × Nat × Nat) := [(7215929344,112845708884984,112846096682556)]
theorem point_links_checked55023 : (cuts55023.take 1).map (fun c => (7215906817-1+2*2^10*c.k,112845670540614+c.lower,112846058338164+c.upper)) = pointBounds55023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000156
