import PlattAssemblyKernel
import PlattCertificates.Count131072.C068000
import PlattCertificates.Count131072.C068001
import PlattCertificates.Count131072.C068002
import PlattCertificates.Count131072.C068003
import PlattCertificates.Count131072.C068004
import PlattCertificates.Count131072.C068005
import PlattCertificates.Count131072.C068006
import PlattCertificates.Count131072.C068007
import PlattCertificates.Count131072.C068008
import PlattCertificates.Count131072.C068009
import PlattCertificates.Count131072.C068010
import PlattCertificates.Count131072.C068011
import PlattCertificates.Count131072.C068012
import PlattCertificates.Count131072.C068013
import PlattCertificates.Count131072.C068014
import PlattCertificates.Count131072.C068015
import PlattCertificates.Count131072.C068016
import PlattCertificates.Count131072.C068017
import PlattCertificates.Count131072.C068018
import PlattCertificates.Count131072.C068019
import PlattCertificates.Count131072.C068020
import PlattCertificates.Count131072.C068021
import PlattCertificates.Count131072.C068022
import PlattCertificates.Count131072.C068023
import PlattCertificates.Count131072.C068024
import PlattCertificates.Count131072.C068025
import PlattCertificates.Count131072.C068026
import PlattCertificates.Count131072.C068027
import PlattCertificates.Count131072.C068028
import PlattCertificates.Count131072.C068029
import PlattCertificates.Count131072.C068030
import PlattCertificates.Count131072.C068031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68000 : List PrefixCut := [⟨64,181475652,181475759⟩]
theorem checked68000 : checkPrefixCuts (2^48) 8916828161 10 Manual.Count131072.C068000.packed 64 cuts68000 = true := by
 decide +kernel
def cuts68001 : List PrefixCut := [⟨27,75032727,75032771⟩,
⟨64,180746968,180747074⟩]
theorem checked68001 : checkPrefixCuts (2^48) 8916959233 10 Manual.Count131072.C068001.packed 64 cuts68001 = true := by
 decide +kernel
def pointBounds68001 : List (Nat × Nat × Nat) := [(8917014528,115458253383200,115458642679937)]
theorem point_links_checked68001 : (cuts68001.take 1).map (fun c => (8916959233-1+2*2^10*c.k,115458178350473+c.lower,115458567647166+c.upper)) = pointBounds68001 := by
 decide +kernel
def cuts68002 : List PrefixCut := [⟨64,179292290,179292397⟩]
theorem checked68002 : checkPrefixCuts (2^48) 8917090305 10 Manual.Count131072.C068002.packed 64 cuts68002 = true := by
 decide +kernel
def cuts68003 : List PrefixCut := [⟨36,101608328,101608392⟩,
⟨64,181846432,181846542⟩]
theorem checked68003 : checkPrefixCuts (2^48) 8917221377 10 Manual.Count131072.C068003.packed 64 cuts68003 = true := by
 decide +kernel
def pointBounds68003 : List (Nat × Nat × Nat) := [(8917295104,115458639998059,115459029295029)]
theorem point_links_checked68003 : (cuts68003.take 1).map (fun c => (8917221377-1+2*2^10*c.k,115458538389731+c.lower,115458927686637+c.upper)) = pointBounds68003 := by
 decide +kernel
def cuts68004 : List PrefixCut := [⟨64,181938456,181938566⟩]
theorem checked68004 : checkPrefixCuts (2^48) 8917352449 10 Manual.Count131072.C068004.packed 64 cuts68004 = true := by
 decide +kernel
def cuts68005 : List PrefixCut := [⟨45,126130636,126130708⟩,
⟨64,178400604,178400705⟩]
theorem checked68005 : checkPrefixCuts (2^48) 8917483521 10 Manual.Count131072.C068005.packed 64 cuts68005 = true := by
 decide +kernel
def pointBounds68005 : List (Nat × Nat × Nat) := [(8917575680,115459028305255,115459417602453)]
theorem point_links_checked68005 : (cuts68005.take 1).map (fun c => (8917483521-1+2*2^10*c.k,115458902174619+c.lower,115459291471745+c.upper)) = pointBounds68005 := by
 decide +kernel
def cuts68006 : List PrefixCut := [⟨64,179660519,179660620⟩]
theorem checked68006 : checkPrefixCuts (2^48) 8917614593 10 Manual.Count131072.C068006.packed 64 cuts68006 = true := by
 decide +kernel
def cuts68007 : List PrefixCut := [⟨54,151093334,151093423⟩,
⟨64,179531624,179531731⟩]
theorem checked68007 : checkPrefixCuts (2^48) 8917745665 10 Manual.Count131072.C068007.packed 64 cuts68007 = true := by
 decide +kernel
def pointBounds68007 : List (Nat × Nat × Nat) := [(8917856256,115459411329076,115459800626493)]
theorem point_links_checked68007 : (cuts68007.take 1).map (fun c => (8917745665-1+2*2^10*c.k,115459260235742+c.lower,115459649533070+c.upper)) = pointBounds68007 := by
 decide +kernel
def cuts68008 : List PrefixCut := [⟨64,179718369,179718477⟩]
theorem checked68008 : checkPrefixCuts (2^48) 8917876737 10 Manual.Count131072.C068008.packed 64 cuts68008 = true := by
 decide +kernel
def cuts68009 : List PrefixCut := [⟨63,178895131,178895231⟩,
⟨64,181262286,181262388⟩]
theorem checked68009 : checkPrefixCuts (2^48) 8918007809 10 Manual.Count131072.C068009.packed 64 cuts68009 = true := by
 decide +kernel
def pointBounds68009 : List (Nat × Nat × Nat) := [(8918136832,115459798380866,115460187678509)]
theorem point_links_checked68009 : (cuts68009.take 1).map (fun c => (8918007809-1+2*2^10*c.k,115459619485735+c.lower,115460008783278+c.upper)) = pointBounds68009 := by
 decide +kernel
def cuts68010 : List PrefixCut := [⟨64,180533700,180533803⟩]
theorem checked68010 : checkPrefixCuts (2^48) 8918138881 10 Manual.Count131072.C068010.packed 64 cuts68010 = true := by
 decide +kernel
def cuts68011 : List PrefixCut := [⟨64,179331713,179331816⟩]
theorem checked68011 : checkPrefixCuts (2^48) 8918269953 10 Manual.Count131072.C068011.packed 64 cuts68011 = true := by
 decide +kernel
def cuts68012 : List PrefixCut := [⟨8,22471510,22471523⟩,
⟨64,180717739,180717850⟩]
theorem checked68012 : checkPrefixCuts (2^48) 8918401025 10 Manual.Count131072.C068012.packed 64 cuts68012 = true := by
 decide +kernel
def pointBounds68012 : List (Nat × Nat × Nat) := [(8918417408,115460183084944,115460572382808)]
theorem point_links_checked68012 : (cuts68012.take 1).map (fun c => (8918401025-1+2*2^10*c.k,115460160613434+c.lower,115460549911285+c.upper)) = pointBounds68012 := by
 decide +kernel
def cuts68013 : List PrefixCut := [⟨64,181409431,181409534⟩]
theorem checked68013 : checkPrefixCuts (2^48) 8918532097 10 Manual.Count131072.C068013.packed 64 cuts68013 = true := by
 decide +kernel
def cuts68014 : List PrefixCut := [⟨17,48886671,48886701⟩,
⟨64,182101080,182101188⟩]
theorem checked68014 : checkPrefixCuts (2^48) 8918663169 10 Manual.Count131072.C068014.packed 64 cuts68014 = true := by
 decide +kernel
def pointBounds68014 : List (Nat × Nat × Nat) := [(8918697984,115460571627275,115460960925370)]
theorem point_links_checked68014 : (cuts68014.take 1).map (fun c => (8918663169-1+2*2^10*c.k,115460522740604+c.lower,115460912038669+c.upper)) = pointBounds68014 := by
 decide +kernel
def cuts68015 : List PrefixCut := [⟨64,179352722,179352827⟩]
theorem checked68015 : checkPrefixCuts (2^48) 8918794241 10 Manual.Count131072.C068015.packed 64 cuts68015 = true := by
 decide +kernel
def cuts68016 : List PrefixCut := [⟨26,73091080,73091126⟩,
⟨64,180296860,180296969⟩]
theorem checked68016 : checkPrefixCuts (2^48) 8918925313 10 Manual.Count131072.C068016.packed 64 cuts68016 = true := by
 decide +kernel
def pointBounds68016 : List (Nat × Nat × Nat) := [(8918978560,115460957285486,115461346583810)]
theorem point_links_checked68016 : (cuts68016.take 1).map (fun c => (8918925313-1+2*2^10*c.k,115460884194406+c.lower,115461273492684+c.upper)) = pointBounds68016 := by
 decide +kernel
def cuts68017 : List PrefixCut := [⟨64,180799155,180799254⟩]
theorem checked68017 : checkPrefixCuts (2^48) 8919056385 10 Manual.Count131072.C068017.packed 64 cuts68017 = true := by
 decide +kernel
def cuts68018 : List PrefixCut := [⟨35,97388699,97388756⟩,
⟨64,179755073,179755180⟩]
theorem checked68018 : checkPrefixCuts (2^48) 8919187457 10 Manual.Count131072.C068018.packed 64 cuts68018 = true := by
 decide +kernel
def pointBounds68018 : List (Nat × Nat × Nat) := [(8919259136,115461342679120,115461731977663)]
theorem point_links_checked68018 : (cuts68018.take 1).map (fun c => (8919187457-1+2*2^10*c.k,115461245290421+c.lower,115461634588907+c.upper)) = pointBounds68018 := by
 decide +kernel
def cuts68019 : List PrefixCut := [⟨64,179436864,179436970⟩]
theorem checked68019 : checkPrefixCuts (2^48) 8919318529 10 Manual.Count131072.C068019.packed 64 cuts68019 = true := by
 decide +kernel
def cuts68020 : List PrefixCut := [⟨44,123262686,123262763⟩,
⟨64,179686668,179686780⟩]
theorem checked68020 : checkPrefixCuts (2^48) 8919449601 10 Manual.Count131072.C068020.packed 64 cuts68020 = true := by
 decide +kernel
def pointBounds68020 : List (Nat × Nat × Nat) := [(8919539712,115461727745044,115462117043820)]
theorem point_links_checked68020 : (cuts68020.take 1).map (fun c => (8919449601-1+2*2^10*c.k,115461604482358+c.lower,115461993781057+c.upper)) = pointBounds68020 := by
 decide +kernel
def cuts68021 : List PrefixCut := [⟨64,178548007,178548109⟩]
theorem checked68021 : checkPrefixCuts (2^48) 8919580673 10 Manual.Count131072.C068021.packed 64 cuts68021 = true := by
 decide +kernel
def cuts68022 : List PrefixCut := [⟨53,150081808,150081896⟩,
⟨64,181574774,181574880⟩]
theorem checked68022 : checkPrefixCuts (2^48) 8919711745 10 Manual.Count131072.C068022.packed 64 cuts68022 = true := by
 decide +kernel
def pointBounds68022 : List (Nat × Nat × Nat) := [(8919820288,115462112798841,115462502097842)]
theorem point_links_checked68022 : (cuts68022.take 1).map (fun c => (8919711745-1+2*2^10*c.k,115461962717033+c.lower,115462352015946+c.upper)) = pointBounds68022 := by
 decide +kernel
def cuts68023 : List PrefixCut := [⟨64,179931206,179931309⟩]
theorem checked68023 : checkPrefixCuts (2^48) 8919842817 10 Manual.Count131072.C068023.packed 64 cuts68023 = true := by
 decide +kernel
def cuts68024 : List PrefixCut := [⟨62,174721973,174722073⟩,
⟨64,180559670,180559773⟩]
theorem checked68024 : checkPrefixCuts (2^48) 8919973889 10 Manual.Count131072.C068024.packed 64 cuts68024 = true := by
 decide +kernel
def pointBounds68024 : List (Nat × Nat × Nat) := [(8920100864,115462498944986,115462888244208)]
theorem point_links_checked68024 : (cuts68024.take 1).map (fun c => (8919973889-1+2*2^10*c.k,115462324223013+c.lower,115462713522135+c.upper)) = pointBounds68024 := by
 decide +kernel
def cuts68025 : List PrefixCut := [⟨64,180493897,180494004⟩]
theorem checked68025 : checkPrefixCuts (2^48) 8920104961 10 Manual.Count131072.C068025.packed 64 cuts68025 = true := by
 decide +kernel
def cuts68026 : List PrefixCut := [⟨64,181217008,181217115⟩]
theorem checked68026 : checkPrefixCuts (2^48) 8920236033 10 Manual.Count131072.C068026.packed 64 cuts68026 = true := by
 decide +kernel
def cuts68027 : List PrefixCut := [⟨7,19248034,19248046⟩,
⟨64,179257998,179258106⟩]
theorem checked68027 : checkPrefixCuts (2^48) 8920367105 10 Manual.Count131072.C068027.packed 64 cuts68027 = true := by
 decide +kernel
def pointBounds68027 : List (Nat × Nat × Nat) := [(8920381440,115462885741622,115463275041073)]
theorem point_links_checked68027 : (cuts68027.take 1).map (fun c => (8920367105-1+2*2^10*c.k,115462866493588+c.lower,115463255793027+c.upper)) = pointBounds68027 := by
 decide +kernel
def cuts68028 : List PrefixCut := [⟨64,182221393,182221504⟩]
theorem checked68028 : checkPrefixCuts (2^48) 8920498177 10 Manual.Count131072.C068028.packed 64 cuts68028 = true := by
 decide +kernel
def cuts68029 : List PrefixCut := [⟨16,44142923,44142949⟩,
⟨64,178968741,178968846⟩]
theorem checked68029 : checkPrefixCuts (2^48) 8920629249 10 Manual.Count131072.C068029.packed 64 cuts68029 = true := by
 decide +kernel
def pointBounds68029 : List (Nat × Nat × Nat) := [(8920662016,115463272115902,115463661415586)]
theorem point_links_checked68029 : (cuts68029.take 1).map (fun c => (8920629249-1+2*2^10*c.k,115463227972979+c.lower,115463617272637+c.upper)) = pointBounds68029 := by
 decide +kernel
def cuts68030 : List PrefixCut := [⟨64,181332573,181332678⟩]
theorem checked68030 : checkPrefixCuts (2^48) 8920760321 10 Manual.Count131072.C068030.packed 64 cuts68030 = true := by
 decide +kernel
def cuts68031 : List PrefixCut := [⟨25,72380839,72380882⟩,
⟨64,181203707,181203813⟩]
theorem checked68031 : checkPrefixCuts (2^48) 8920891393 10 Manual.Count131072.C068031.packed 64 cuts68031 = true := by
 decide +kernel
def pointBounds68031 : List (Nat × Nat × Nat) := [(8920942592,115463660655132,115464049955043)]
theorem point_links_checked68031 : (cuts68031.take 1).map (fun c => (8920891393-1+2*2^10*c.k,115463588274293+c.lower,115463977574161+c.upper)) = pointBounds68031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000250
