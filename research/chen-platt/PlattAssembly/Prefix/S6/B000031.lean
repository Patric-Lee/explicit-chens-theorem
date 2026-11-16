import PlattAssemblyKernel
import PlattCertificates.Count131072.C050992
import PlattCertificates.Count131072.C050993
import PlattCertificates.Count131072.C050994
import PlattCertificates.Count131072.C050995
import PlattCertificates.Count131072.C050996
import PlattCertificates.Count131072.C050997
import PlattCertificates.Count131072.C050998
import PlattCertificates.Count131072.C050999
import PlattCertificates.Count131072.C051000
import PlattCertificates.Count131072.C051001
import PlattCertificates.Count131072.C051002
import PlattCertificates.Count131072.C051003
import PlattCertificates.Count131072.C051004
import PlattCertificates.Count131072.C051005
import PlattCertificates.Count131072.C051006
import PlattCertificates.Count131072.C051007
import PlattCertificates.Count131072.C051008
import PlattCertificates.Count131072.C051009
import PlattCertificates.Count131072.C051010
import PlattCertificates.Count131072.C051011
import PlattCertificates.Count131072.C051012
import PlattCertificates.Count131072.C051013
import PlattCertificates.Count131072.C051014
import PlattCertificates.Count131072.C051015
import PlattCertificates.Count131072.C051016
import PlattCertificates.Count131072.C051017
import PlattCertificates.Count131072.C051018
import PlattCertificates.Count131072.C051019
import PlattCertificates.Count131072.C051020
import PlattCertificates.Count131072.C051021
import PlattCertificates.Count131072.C051022
import PlattCertificates.Count131072.C051023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50992 : List PrefixCut := [⟨64,242179794,242179933⟩]
theorem checked50992 : checkPrefixCuts (2^48) 6687555585 10 Manual.Count131072.C050992.packed 64 cuts50992 = true := by
 decide +kernel
def cuts50993 : List PrefixCut := [⟨28,105010436,105010497⟩,
⟨64,243269307,243269447⟩]
theorem checked50993 : checkPrefixCuts (2^48) 6687686657 10 Manual.Count131072.C050993.packed 64 cuts50993 = true := by
 decide +kernel
def pointBounds50993 : List (Nat × Nat × Nat) := [(6687744000,111901630178657,111902017439954)]
theorem point_links_checked50993 : (cuts50993.take 1).map (fun c => (6687686657-1+2*2^10*c.k,111901525168221+c.lower,111901912429457+c.upper)) = pointBounds50993 := by
 decide +kernel
def cuts50994 : List PrefixCut := [⟨64,241202255,241202394⟩]
theorem checked50994 : checkPrefixCuts (2^48) 6687817729 10 Manual.Count131072.C050994.packed 64 cuts50994 = true := by
 decide +kernel
def cuts50995 : List PrefixCut := [⟨3,11615974,11615981⟩,
⟨64,243848988,243849129⟩]
theorem checked50995 : checkPrefixCuts (2^48) 6687948801 10 Manual.Count131072.C050995.packed 64 cuts50995 = true := by
 decide +kernel
def pointBounds50995 : List (Nat × Nat × Nat) := [(6687954944,111902021255757,111902408517279)]
theorem point_links_checked50995 : (cuts50995.take 1).map (fun c => (6687948801-1+2*2^10*c.k,111902009639783+c.lower,111902396901298+c.upper)) = pointBounds50995 := by
 decide +kernel
def cuts50996 : List PrefixCut := [⟨42,159000099,159000187⟩,
⟨64,243044588,243044722⟩]
theorem checked50996 : checkPrefixCuts (2^48) 6688079873 10 Manual.Count131072.C050996.packed 64 cuts50996 = true := by
 decide +kernel
def pointBounds50996 : List (Nat × Nat × Nat) := [(6688165888,111902412488870,111902799750614)]
theorem point_links_checked50996 : (cuts50996.take 1).map (fun c => (6688079873-1+2*2^10*c.k,111902253488771+c.lower,111902640750427+c.upper)) = pointBounds50996 := by
 decide +kernel
def cuts50997 : List PrefixCut := [⟨64,242871478,242871619⟩]
theorem checked50997 : checkPrefixCuts (2^48) 6688210945 10 Manual.Count131072.C050997.packed 64 cuts50997 = true := by
 decide +kernel
def cuts50998 : List PrefixCut := [⟨17,64178555,64178591⟩,
⟨64,243624226,243624361⟩]
theorem checked50998 : checkPrefixCuts (2^48) 6688342017 10 Manual.Count131072.C050998.packed 64 cuts50998 = true := by
 decide +kernel
def pointBounds50998 : List (Nat × Nat × Nat) := [(6688376832,111902803583392,111903190845359)]
theorem point_links_checked50998 : (cuts50998.take 1).map (fun c => (6688342017-1+2*2^10*c.k,111902739404837+c.lower,111903126666768+c.upper)) = pointBounds50998 := by
 decide +kernel
def cuts50999 : List PrefixCut := [⟨56,212225695,212225814⟩,
⟨64,243535304,243535440⟩]
theorem checked50999 : checkPrefixCuts (2^48) 6688473089 10 Manual.Count131072.C050999.packed 64 cuts50999 = true := by
 decide +kernel
def pointBounds50999 : List (Nat × Nat × Nat) := [(6688587776,111903195254758,111903582516943)]
theorem point_links_checked50999 : (cuts50999.take 1).map (fun c => (6688473089-1+2*2^10*c.k,111902983029063+c.lower,111903370291129+c.upper)) = pointBounds50999 := by
 decide +kernel
def cuts51000 : List PrefixCut := [⟨64,243614672,243614807⟩]
theorem checked51000 : checkPrefixCuts (2^48) 6688604161 10 Manual.Count131072.C051000.packed 64 cuts51000 = true := by
 decide +kernel
def cuts51001 : List PrefixCut := [⟨31,117197630,117197695⟩,
⟨64,241590014,241590148⟩]
theorem checked51001 : checkPrefixCuts (2^48) 6688735233 10 Manual.Count131072.C051001.packed 64 cuts51001 = true := by
 decide +kernel
def pointBounds51001 : List (Nat × Nat × Nat) := [(6688798720,111903587376669,111903974639071)]
theorem point_links_checked51001 : (cuts51001.take 1).map (fun c => (6688735233-1+2*2^10*c.k,111903470179039+c.lower,111903857441376+c.upper)) = pointBounds51001 := by
 decide +kernel
def cuts51002 : List PrefixCut := [⟨64,250169741,250169884⟩]
theorem checked51002 : checkPrefixCuts (2^48) 6688866305 10 Manual.Count131072.C051002.packed 64 cuts51002 = true := by
 decide +kernel
def cuts51003 : List PrefixCut := [⟨6,22891653,22891666⟩,
⟨64,238929500,238929633⟩]
theorem checked51003 : checkPrefixCuts (2^48) 6688997377 10 Manual.Count131072.C051003.packed 64 cuts51003 = true := by
 decide +kernel
def pointBounds51003 : List (Nat × Nat × Nat) := [(6689009664,111903984830447,111904372093074)]
theorem point_links_checked51003 : (cuts51003.take 1).map (fun c => (6688997377-1+2*2^10*c.k,111903961938794+c.lower,111904349201408+c.upper)) = pointBounds51003 := by
 decide +kernel
def cuts51004 : List PrefixCut := [⟨45,170126080,170126177⟩,
⟨64,243974297,243974435⟩]
theorem checked51004 : checkPrefixCuts (2^48) 6689128449 10 Manual.Count131072.C051004.packed 64 cuts51004 = true := by
 decide +kernel
def pointBounds51004 : List (Nat × Nat × Nat) := [(6689220608,111904370994374,111904758257218)]
theorem point_links_checked51004 : (cuts51004.take 1).map (fun c => (6689128449-1+2*2^10*c.k,111904200868294+c.lower,111904588131041+c.upper)) = pointBounds51004 := by
 decide +kernel
def cuts51005 : List PrefixCut := [⟨64,244684868,244685004⟩]
theorem checked51005 : checkPrefixCuts (2^48) 6689259521 10 Manual.Count131072.C051005.packed 64 cuts51005 = true := by
 decide +kernel
def cuts51006 : List PrefixCut := [⟨20,75487356,75487398⟩,
⟨64,243712266,243712405⟩]
theorem checked51006 : checkPrefixCuts (2^48) 6689390593 10 Manual.Count131072.C051006.packed 64 cuts51006 = true := by
 decide +kernel
def pointBounds51006 : List (Nat × Nat × Nat) := [(6689431552,111904765014815,111905152277878)]
theorem point_links_checked51006 : (cuts51006.take 1).map (fun c => (6689390593-1+2*2^10*c.k,111904689527459+c.lower,111905076790480+c.upper)) = pointBounds51006 := by
 decide +kernel
def cuts51007 : List PrefixCut := [⟨59,224941518,224941645⟩,
⟨64,243917881,243918018⟩]
theorem checked51007 : checkPrefixCuts (2^48) 6689521665 10 Manual.Count131072.C051007.packed 64 cuts51007 = true := by
 decide +kernel
def pointBounds51007 : List (Nat × Nat × Nat) := [(6689642496,111905158181243,111905545444530)]
theorem point_links_checked51007 : (cuts51007.take 1).map (fun c => (6689521665-1+2*2^10*c.k,111904933239725+c.lower,111905320502885+c.upper)) = pointBounds51007 := by
 decide +kernel
def cuts51008 : List PrefixCut := [⟨64,242819127,242819267⟩]
theorem checked51008 : checkPrefixCuts (2^48) 6689652737 10 Manual.Count131072.C051008.packed 64 cuts51008 = true := by
 decide +kernel
def cuts51009 : List PrefixCut := [⟨34,127824201,127824272⟩,
⟨64,244413205,244413343⟩]
theorem checked51009 : checkPrefixCuts (2^48) 6689783809 10 Manual.Count131072.C051009.packed 64 cuts51009 = true := by
 decide +kernel
def pointBounds51009 : List (Nat × Nat × Nat) := [(6689853440,111905547800934,111905935064442)]
theorem point_links_checked51009 : (cuts51009.take 1).map (fun c => (6689783809-1+2*2^10*c.k,111905419976733+c.lower,111905807240170+c.upper)) = pointBounds51009 := by
 decide +kernel
def cuts51010 : List PrefixCut := [⟨64,244113924,244114065⟩]
theorem checked51010 : checkPrefixCuts (2^48) 6689914881 10 Manual.Count131072.C051010.packed 64 cuts51010 = true := by
 decide +kernel
def cuts51011 : List PrefixCut := [⟨9,35425995,35426016⟩,
⟨64,247811578,247811721⟩]
theorem checked51011 : checkPrefixCuts (2^48) 6690045953 10 Manual.Count131072.C051011.packed 64 cuts51011 = true := by
 decide +kernel
def pointBounds51011 : List (Nat × Nat × Nat) := [(6690064384,111905943929857,111906331193594)]
theorem point_links_checked51011 : (cuts51011.take 1).map (fun c => (6690045953-1+2*2^10*c.k,111905908503862+c.lower,111906295767578+c.upper)) = pointBounds51011 := by
 decide +kernel
def cuts51012 : List PrefixCut := [⟨48,182384520,182384625⟩,
⟨64,244525073,244525214⟩]
theorem checked51012 : checkPrefixCuts (2^48) 6690177025 10 Manual.Count131072.C051012.packed 64 cuts51012 = true := by
 decide +kernel
def pointBounds51012 : List (Nat × Nat × Nat) := [(6690275328,111906338699960,111906725963924)]
theorem point_links_checked51012 : (cuts51012.take 1).map (fun c => (6690177025-1+2*2^10*c.k,111906156315440+c.lower,111906543579299+c.upper)) = pointBounds51012 := by
 decide +kernel
def cuts51013 : List PrefixCut := [⟨64,242542941,242543081⟩]
theorem checked51013 : checkPrefixCuts (2^48) 6690308097 10 Manual.Count131072.C051013.packed 64 cuts51013 = true := by
 decide +kernel
def cuts51014 : List PrefixCut := [⟨23,87381600,87381652⟩,
⟨64,245356908,245357049⟩]
theorem checked51014 : checkPrefixCuts (2^48) 6690439169 10 Manual.Count131072.C051014.packed 64 cuts51014 = true := by
 decide +kernel
def pointBounds51014 : List (Nat × Nat × Nat) := [(6690486272,111906730765054,111907118029246)]
theorem point_links_checked51014 : (cuts51014.take 1).map (fun c => (6690439169-1+2*2^10*c.k,111906643383454+c.lower,111907030647594+c.upper)) = pointBounds51014 := by
 decide +kernel
def cuts51015 : List PrefixCut := [⟨62,237106456,237106586⟩,
⟨64,244805189,244805323⟩]
theorem checked51015 : checkPrefixCuts (2^48) 6690570241 10 Manual.Count131072.C051015.packed 64 cuts51015 = true := by
 decide +kernel
def pointBounds51015 : List (Nat × Nat × Nat) := [(6690697216,111907125846818,111907513111229)]
theorem point_links_checked51015 : (cuts51015.take 1).map (fun c => (6690570241-1+2*2^10*c.k,111906888740362+c.lower,111907276004643+c.upper)) = pointBounds51015 := by
 decide +kernel
def cuts51016 : List PrefixCut := [⟨64,241308677,241308815⟩]
theorem checked51016 : checkPrefixCuts (2^48) 6690701313 10 Manual.Count131072.C051016.packed 64 cuts51016 = true := by
 decide +kernel
def cuts51017 : List PrefixCut := [⟨37,138447430,138447514⟩,
⟨64,239284635,239284778⟩]
theorem checked51017 : checkPrefixCuts (2^48) 6690832385 10 Manual.Count131072.C051017.packed 64 cuts51017 = true := by
 decide +kernel
def pointBounds51017 : List (Nat × Nat × Nat) := [(6690908160,111907513301658,111907900566295)]
theorem point_links_checked51017 : (cuts51017.take 1).map (fun c => (6690832385-1+2*2^10*c.k,111907374854228+c.lower,111907762118781+c.upper)) = pointBounds51017 := by
 decide +kernel
def cuts51018 : List PrefixCut := [⟨64,245884570,245884709⟩]
theorem checked51018 : checkPrefixCuts (2^48) 6690963457 10 Manual.Count131072.C051018.packed 64 cuts51018 = true := by
 decide +kernel
def cuts51019 : List PrefixCut := [⟨12,46105449,46105476⟩,
⟨64,247394145,247394286⟩]
theorem checked51019 : checkPrefixCuts (2^48) 6691094529 10 Manual.Count131072.C051019.packed 64 cuts51019 = true := by
 decide +kernel
def pointBounds51019 : List (Nat × Nat × Nat) := [(6691119104,111907906128882,111908293393744)]
theorem point_links_checked51019 : (cuts51019.take 1).map (fun c => (6691094529-1+2*2^10*c.k,111907860023433+c.lower,111908247288268+c.upper)) = pointBounds51019 := by
 decide +kernel
def cuts51020 : List PrefixCut := [⟨51,194050176,194050287⟩,
⟨64,243224779,243224917⟩]
theorem checked51020 : checkPrefixCuts (2^48) 6691225601 10 Manual.Count131072.C051020.packed 64 cuts51020 = true := by
 decide +kernel
def pointBounds51020 : List (Nat × Nat × Nat) := [(6691330048,111908301467754,111908688732841)]
theorem point_links_checked51020 : (cuts51020.take 1).map (fun c => (6691225601-1+2*2^10*c.k,111908107417578+c.lower,111908494682554+c.upper)) = pointBounds51020 := by
 decide +kernel
def cuts51021 : List PrefixCut := [⟨64,240191309,240191453⟩]
theorem checked51021 : checkPrefixCuts (2^48) 6691356673 10 Manual.Count131072.C051021.packed 64 cuts51021 = true := by
 decide +kernel
def cuts51022 : List PrefixCut := [⟨26,98514952,98515005⟩,
⟨64,245781158,245781298⟩]
theorem checked51022 : checkPrefixCuts (2^48) 6691487745 10 Manual.Count131072.C051022.packed 64 cuts51022 = true := by
 decide +kernel
def pointBounds51022 : List (Nat × Nat × Nat) := [(6691540992,111908689348618,111909076613929)]
theorem point_links_checked51022 : (cuts51022.take 1).map (fun c => (6691487745-1+2*2^10*c.k,111908590833666+c.lower,111908978098924+c.upper)) = pointBounds51022 := by
 decide +kernel
def cuts51023 : List PrefixCut := [⟨64,244682718,244682857⟩]
theorem checked51023 : checkPrefixCuts (2^48) 6691618817 10 Manual.Count131072.C051023.packed 64 cuts51023 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000031
