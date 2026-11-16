import PlattAssemblyKernel
import PlattCertificates.Count131072.C050000
import PlattCertificates.Count131072.C050001
import PlattCertificates.Count131072.C050002
import PlattCertificates.Count131072.C050003
import PlattCertificates.Count131072.C050004
import PlattCertificates.Count131072.C050005
import PlattCertificates.Count131072.C050006
import PlattCertificates.Count131072.C050007
import PlattCertificates.Count131072.C050008
import PlattCertificates.Count131072.C050009
import PlattCertificates.Count131072.C050010
import PlattCertificates.Count131072.C050011
import PlattCertificates.Count131072.C050012
import PlattCertificates.Count131072.C050013
import PlattCertificates.Count131072.C050014
import PlattCertificates.Count131072.C050015
import PlattCertificates.Count131072.C050016
import PlattCertificates.Count131072.C050017
import PlattCertificates.Count131072.C050018
import PlattCertificates.Count131072.C050019
import PlattCertificates.Count131072.C050020
import PlattCertificates.Count131072.C050021
import PlattCertificates.Count131072.C050022
import PlattCertificates.Count131072.C050023
import PlattCertificates.Count131072.C050024
import PlattCertificates.Count131072.C050025
import PlattCertificates.Count131072.C050026
import PlattCertificates.Count131072.C050027
import PlattCertificates.Count131072.C050028
import PlattCertificates.Count131072.C050029
import PlattCertificates.Count131072.C050030
import PlattCertificates.Count131072.C050031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50000 : List PrefixCut := [⟨12,47774218,47774244⟩,
⟨64,249642933,249643075⟩]
theorem checked50000 : checkPrefixCuts (2^48) 6557532161 10 Manual.Count131072.C050000.packed 64 cuts50000 = true := by
 decide +kernel
def pointBounds50000 : List (Nat × Nat × Nat) := [(6557556736,111656885580465,111657272702584)]
theorem point_links_checked50000 : (cuts50000.take 1).map (fun c => (6557532161-1+2*2^10*c.k,111656837806247+c.lower,111657224928340+c.upper)) = pointBounds50000 := by
 decide +kernel
def cuts50001 : List PrefixCut := [⟨49,186069993,186070102⟩,
⟨64,246075356,246075498⟩]
theorem checked50001 : checkPrefixCuts (2^48) 6557663233 10 Manual.Count131072.C050001.packed 64 cuts50001 = true := by
 decide +kernel
def pointBounds50001 : List (Nat × Nat × Nat) := [(6557763584,111657273519173,111657660641517)]
theorem point_links_checked50001 : (cuts50001.take 1).map (fun c => (6557663233-1+2*2^10*c.k,111657087449180+c.lower,111657474571415+c.upper)) = pointBounds50001 := by
 decide +kernel
def cuts50002 : List PrefixCut := [⟨64,250019280,250019422⟩]
theorem checked50002 : checkPrefixCuts (2^48) 6557794305 10 Manual.Count131072.C050002.packed 64 cuts50002 = true := by
 decide +kernel
def cuts50003 : List PrefixCut := [⟨22,85541915,85541965⟩,
⟨64,247653591,247653737⟩]
theorem checked50003 : checkPrefixCuts (2^48) 6557925377 10 Manual.Count131072.C050003.packed 64 cuts50003 = true := by
 decide +kernel
def pointBounds50003 : List (Nat × Nat × Nat) := [(6557970432,111657669085731,111658056208300)]
theorem point_links_checked50003 : (cuts50003.take 1).map (fun c => (6557925377-1+2*2^10*c.k,111657583543816+c.lower,111657970666335+c.upper)) = pointBounds50003 := by
 decide +kernel
def cuts50004 : List PrefixCut := [⟨59,227433470,227433597⟩,
⟨64,246532714,246532852⟩]
theorem checked50004 : checkPrefixCuts (2^48) 6558056449 10 Manual.Count131072.C050004.packed 64 cuts50004 = true := by
 decide +kernel
def pointBounds50004 : List (Nat × Nat × Nat) := [(6558177280,111658058630877,111658445753669)]
theorem point_links_checked50004 : (cuts50004.take 1).map (fun c => (6558056449-1+2*2^10*c.k,111657831197407+c.lower,111658218320072+c.upper)) = pointBounds50004 := by
 decide +kernel
def cuts50005 : List PrefixCut := [⟨64,247042856,247042997⟩]
theorem checked50005 : checkPrefixCuts (2^48) 6558187521 10 Manual.Count131072.C050005.packed 64 cuts50005 = true := by
 decide +kernel
def cuts50006 : List PrefixCut := [⟨32,125579668,125579735⟩,
⟨64,250256789,250256926⟩]
theorem checked50006 : checkPrefixCuts (2^48) 6558318593 10 Manual.Count131072.C050006.packed 64 cuts50006 = true := by
 decide +kernel
def pointBounds50006 : List (Nat × Nat × Nat) := [(6558384128,111658450352645,111658837475656)]
theorem point_links_checked50006 : (cuts50006.take 1).map (fun c => (6558318593-1+2*2^10*c.k,111658324772977+c.lower,111658711895921+c.upper)) = pointBounds50006 := by
 decide +kernel
def cuts50007 : List PrefixCut := [⟨64,246475065,246475207⟩]
theorem checked50007 : checkPrefixCuts (2^48) 6558449665 10 Manual.Count131072.C050007.packed 64 cuts50007 = true := by
 decide +kernel
def cuts50008 : List PrefixCut := [⟨5,18969320,18969330⟩,
⟨64,248615948,248616090⟩]
theorem checked50008 : checkPrefixCuts (2^48) 6558580737 10 Manual.Count131072.C050008.packed 64 cuts50008 = true := by
 decide +kernel
def pointBounds50008 : List (Nat × Nat × Nat) := [(6558590976,111658840474151,111659227597384)]
theorem point_links_checked50008 : (cuts50008.take 1).map (fun c => (6558580737-1+2*2^10*c.k,111658821504831+c.lower,111659208628054+c.upper)) = pointBounds50008 := by
 decide +kernel
def cuts50009 : List PrefixCut := [⟨42,164410830,164410924⟩,
⟨64,249125979,249126121⟩]
theorem checked50009 : checkPrefixCuts (2^48) 6558711809 10 Manual.Count131072.C050009.packed 64 cuts50009 = true := by
 decide +kernel
def pointBounds50009 : List (Nat × Nat × Nat) := [(6558797824,111659234531609,111659621655068)]
theorem point_links_checked50009 : (cuts50009.take 1).map (fun c => (6558711809-1+2*2^10*c.k,111659070120779+c.lower,111659457244144+c.upper)) = pointBounds50009 := by
 decide +kernel
def cuts50010 : List PrefixCut := [⟨64,249120996,249121142⟩]
theorem checked50010 : checkPrefixCuts (2^48) 6558842881 10 Manual.Count131072.C050010.packed 64 cuts50010 = true := by
 decide +kernel
def cuts50011 : List PrefixCut := [⟨15,58320632,58320664⟩,
⟨64,248686874,248687014⟩]
theorem checked50011 : checkPrefixCuts (2^48) 6558973953 10 Manual.Count131072.C050011.packed 64 cuts50011 = true := by
 decide +kernel
def pointBounds50011 : List (Nat × Nat × Nat) := [(6559004672,111659626688386,111660013812071)]
theorem point_links_checked50011 : (cuts50011.take 1).map (fun c => (6558973953-1+2*2^10*c.k,111659568367754+c.lower,111659955491407+c.upper)) = pointBounds50011 := by
 decide +kernel
def cuts50012 : List PrefixCut := [⟨52,205683264,205683377⟩,
⟨64,250355523,250355663⟩]
theorem checked50012 : checkPrefixCuts (2^48) 6559105025 10 Manual.Count131072.C050012.packed 64 cuts50012 = true := by
 decide +kernel
def pointBounds50012 : List (Nat × Nat × Nat) := [(6559211520,111660022737892,111660409861798)]
theorem point_links_checked50012 : (cuts50012.take 1).map (fun c => (6559105025-1+2*2^10*c.k,111659817054628+c.lower,111660204178421+c.upper)) = pointBounds50012 := by
 decide +kernel
def cuts50013 : List PrefixCut := [⟨64,252581979,252582125⟩]
theorem checked50013 : checkPrefixCuts (2^48) 6559236097 10 Manual.Count131072.C050013.packed 64 cuts50013 = true := by
 decide +kernel
def cuts50014 : List PrefixCut := [⟨25,96422663,96422720⟩,
⟨64,248114127,248114272⟩]
theorem checked50014 : checkPrefixCuts (2^48) 6559367169 10 Manual.Count131072.C050014.packed 64 cuts50014 = true := by
 decide +kernel
def pointBounds50014 : List (Nat × Nat × Nat) := [(6559418368,111660416414793,111660803538929)]
theorem point_links_checked50014 : (cuts50014.take 1).map (fun c => (6559367169-1+2*2^10*c.k,111660319992130+c.lower,111660707116209+c.upper)) = pointBounds50014 := by
 decide +kernel
def cuts50015 : List PrefixCut := [⟨62,240642776,240642916⟩,
⟨64,248666983,248667127⟩]
theorem checked50015 : checkPrefixCuts (2^48) 6559498241 10 Manual.Count131072.C050015.packed 64 cuts50015 = true := by
 decide +kernel
def pointBounds50015 : List (Nat × Nat × Nat) := [(6559625216,111660808749033,111661195873397)]
theorem point_links_checked50015 : (cuts50015.take 1).map (fun c => (6559498241-1+2*2^10*c.k,111660568106257+c.lower,111660955230481+c.upper)) = pointBounds50015 := by
 decide +kernel
def cuts50016 : List PrefixCut := [⟨64,248619112,248619255⟩]
theorem checked50016 : checkPrefixCuts (2^48) 6559629313 10 Manual.Count131072.C050016.packed 64 cuts50016 = true := by
 decide +kernel
def cuts50017 : List PrefixCut := [⟨35,135936000,135936076⟩,
⟨64,248442512,248442650⟩]
theorem checked50017 : checkPrefixCuts (2^48) 6559760385 10 Manual.Count131072.C050017.packed 64 cuts50017 = true := by
 decide +kernel
def pointBounds50017 : List (Nat × Nat × Nat) := [(6559832064,111661201328352,111661588452939)]
theorem point_links_checked50017 : (cuts50017.take 1).map (fun c => (6559760385-1+2*2^10*c.k,111661065392352+c.lower,111661452516863+c.upper)) = pointBounds50017 := by
 decide +kernel
def cuts50018 : List PrefixCut := [⟨64,250840412,250840552⟩]
theorem checked50018 : checkPrefixCuts (2^48) 6559891457 10 Manual.Count131072.C050018.packed 64 cuts50018 = true := by
 decide +kernel
def cuts50019 : List PrefixCut := [⟨8,31279611,31279627⟩,
⟨64,248904580,248904719⟩]
theorem checked50019 : checkPrefixCuts (2^48) 6560022529 10 Manual.Count131072.C050019.packed 64 cuts50019 = true := by
 decide +kernel
def pointBounds50019 : List (Nat × Nat × Nat) := [(6560038912,111661595954887,111661983079692)]
theorem point_links_checked50019 : (cuts50019.take 1).map (fun c => (6560022529-1+2*2^10*c.k,111661564675276+c.lower,111661951800065+c.upper)) = pointBounds50019 := by
 decide +kernel
def cuts50020 : List PrefixCut := [⟨45,176302604,176302701⟩,
⟨64,249199942,249200080⟩]
theorem checked50020 : checkPrefixCuts (2^48) 6560153601 10 Manual.Count131072.C050020.packed 64 cuts50020 = true := by
 decide +kernel
def pointBounds50020 : List (Nat × Nat × Nat) := [(6560245760,111661989882460,111662377007485)]
theorem point_links_checked50020 : (cuts50020.take 1).map (fun c => (6560153601-1+2*2^10*c.k,111661813579856+c.lower,111662200704784+c.upper)) = pointBounds50020 := by
 decide +kernel
def cuts50021 : List PrefixCut := [⟨64,250053079,250053217⟩]
theorem checked50021 : checkPrefixCuts (2^48) 6560284673 10 Manual.Count131072.C050021.packed 64 cuts50021 = true := by
 decide +kernel
def cuts50022 : List PrefixCut := [⟨18,73024174,73024214⟩,
⟨64,254166932,254167071⟩]
theorem checked50022 : checkPrefixCuts (2^48) 6560415745 10 Manual.Count131072.C050022.packed 64 cuts50022 = true := by
 decide +kernel
def pointBounds50022 : List (Nat × Nat × Nat) := [(6560452608,111662385857051,111662772982295)]
theorem point_links_checked50022 : (cuts50022.take 1).map (fun c => (6560415745-1+2*2^10*c.k,111662312832877+c.lower,111662699958081+c.upper)) = pointBounds50022 := by
 decide +kernel
def cuts50023 : List PrefixCut := [⟨55,212588385,212588504⟩,
⟨64,246825287,246825426⟩]
theorem checked50023 : checkPrefixCuts (2^48) 6560546817 10 Manual.Count131072.C050023.packed 64 cuts50023 = true := by
 decide +kernel
def pointBounds50023 : List (Nat × Nat × Nat) := [(6560659456,111662779588194,111663166713656)]
theorem point_links_checked50023 : (cuts50023.take 1).map (fun c => (6560546817-1+2*2^10*c.k,111662566999809+c.lower,111662954125152+c.upper)) = pointBounds50023 := by
 decide +kernel
def cuts50024 : List PrefixCut := [⟨64,249051330,249051475⟩]
theorem checked50024 : checkPrefixCuts (2^48) 6560677889 10 Manual.Count131072.C050024.packed 64 cuts50024 = true := by
 decide +kernel
def cuts50025 : List PrefixCut := [⟨28,110945309,110945373⟩,
⟨64,250376324,250376467⟩]
theorem checked50025 : checkPrefixCuts (2^48) 6560808961 10 Manual.Count131072.C050025.packed 64 cuts50025 = true := by
 decide +kernel
def pointBounds50025 : List (Nat × Nat × Nat) := [(6560866304,111663173821735,111663560947426)]
theorem point_links_checked50025 : (cuts50025.take 1).map (fun c => (6560808961-1+2*2^10*c.k,111663062876426+c.lower,111663450002053+c.upper)) = pointBounds50025 := by
 decide +kernel
def cuts50026 : List PrefixCut := [⟨64,248440741,248440884⟩]
theorem checked50026 : checkPrefixCuts (2^48) 6560940033 10 Manual.Count131072.C050026.packed 64 cuts50026 = true := by
 decide +kernel
def cuts50027 : List PrefixCut := [⟨1,3946869,3946871⟩,
⟨64,247620682,247620821⟩]
theorem checked50027 : checkPrefixCuts (2^48) 6561071105 10 Manual.Count131072.C050027.packed 64 cuts50027 = true := by
 decide +kernel
def pointBounds50027 : List (Nat × Nat × Nat) := [(6561073152,111663565640360,111663952766275)]
theorem point_links_checked50027 : (cuts50027.take 1).map (fun c => (6561071105-1+2*2^10*c.k,111663561693491+c.lower,111663948819404+c.upper)) = pointBounds50027 := by
 decide +kernel
def cuts50028 : List PrefixCut := [⟨38,148175351,148175433⟩,
⟨64,251776953,251777092⟩]
theorem checked50028 : checkPrefixCuts (2^48) 6561202177 10 Manual.Count131072.C050028.packed 64 cuts50028 = true := by
 decide +kernel
def pointBounds50028 : List (Nat × Nat × Nat) := [(6561280000,111663957489524,111664344615658)]
theorem point_links_checked50028 : (cuts50028.take 1).map (fun c => (6561202177-1+2*2^10*c.k,111663809314173+c.lower,111664196440225+c.upper)) = pointBounds50028 := by
 decide +kernel
def cuts50029 : List PrefixCut := [⟨64,247996856,247996997⟩]
theorem checked50029 : checkPrefixCuts (2^48) 6561333249 10 Manual.Count131072.C050029.packed 64 cuts50029 = true := by
 decide +kernel
def cuts50030 : List PrefixCut := [⟨11,42769416,42769441⟩,
⟨64,249107243,249107390⟩]
theorem checked50030 : checkPrefixCuts (2^48) 6561464321 10 Manual.Count131072.C050030.packed 64 cuts50030 = true := by
 decide +kernel
def pointBounds50030 : List (Nat × Nat × Nat) := [(6561486848,111664351857398,111664738983755)]
theorem point_links_checked50030 : (cuts50030.take 1).map (fun c => (6561464321-1+2*2^10*c.k,111664309087982+c.lower,111664696214314+c.upper)) = pointBounds50030 := by
 decide +kernel
def cuts50031 : List PrefixCut := [⟨48,188060475,188060588⟩,
⟨64,247257753,247257899⟩]
theorem checked50031 : checkPrefixCuts (2^48) 6561595393 10 Manual.Count131072.C050031.packed 64 cuts50031 = true := by
 decide +kernel
def pointBounds50031 : List (Nat × Nat × Nat) := [(6561693696,111664746255700,111665133382292)]
theorem point_links_checked50031 : (cuts50031.take 1).map (fun c => (6561595393-1+2*2^10*c.k,111664558195225+c.lower,111664945321704+c.upper)) = pointBounds50031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000000
