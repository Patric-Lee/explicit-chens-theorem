import PlattAssemblyKernel
import PlattCertificates.Count131072.C055504
import PlattCertificates.Count131072.C055505
import PlattCertificates.Count131072.C055506
import PlattCertificates.Count131072.C055507
import PlattCertificates.Count131072.C055508
import PlattCertificates.Count131072.C055509
import PlattCertificates.Count131072.C055510
import PlattCertificates.Count131072.C055511
import PlattCertificates.Count131072.C055512
import PlattCertificates.Count131072.C055513
import PlattCertificates.Count131072.C055514
import PlattCertificates.Count131072.C055515
import PlattCertificates.Count131072.C055516
import PlattCertificates.Count131072.C055517
import PlattCertificates.Count131072.C055518
import PlattCertificates.Count131072.C055519
import PlattCertificates.Count131072.C055520
import PlattCertificates.Count131072.C055521
import PlattCertificates.Count131072.C055522
import PlattCertificates.Count131072.C055523
import PlattCertificates.Count131072.C055524
import PlattCertificates.Count131072.C055525
import PlattCertificates.Count131072.C055526
import PlattCertificates.Count131072.C055527
import PlattCertificates.Count131072.C055528
import PlattCertificates.Count131072.C055529
import PlattCertificates.Count131072.C055530
import PlattCertificates.Count131072.C055531
import PlattCertificates.Count131072.C055532
import PlattCertificates.Count131072.C055533
import PlattCertificates.Count131072.C055534
import PlattCertificates.Count131072.C055535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55504 : List PrefixCut := [⟨64,223972861,223972987⟩]
theorem checked55504 : checkPrefixCuts (2^48) 7278952449 10 Manual.Count131072.C055504.packed 64 cuts55504 = true := by
 decide +kernel
def cuts55505 : List PrefixCut := [⟨41,139826307,139826386⟩,
⟨64,218671240,218671363⟩]
theorem checked55505 : checkPrefixCuts (2^48) 7279083521 10 Manual.Count131072.C055505.packed 64 cuts55505 = true := by
 decide +kernel
def pointBounds55505 : List (Nat × Nat × Nat) := [(7279167488,112953907204262,112954295063258)]
theorem point_links_checked55505 : (cuts55505.take 1).map (fun c => (7279083521-1+2*2^10*c.k,112953767377955+c.lower,112954155236872+c.upper)) = pointBounds55505 := by
 decide +kernel
def cuts55506 : List PrefixCut := [⟨64,224119492,224119618⟩]
theorem checked55506 : checkPrefixCuts (2^48) 7279214593 10 Manual.Count131072.C055506.packed 64 cuts55506 = true := by
 decide +kernel
def cuts55507 : List PrefixCut := [⟨25,88432513,88432563⟩,
⟨64,222530102,222530228⟩]
theorem checked55507 : checkPrefixCuts (2^48) 7279345665 10 Manual.Count131072.C055507.packed 64 cuts55507 = true := by
 decide +kernel
def pointBounds55507 : List (Nat × Nat × Nat) := [(7279396864,112954298601200,112954686460416)]
theorem point_links_checked55507 : (cuts55507.take 1).map (fun c => (7279345665-1+2*2^10*c.k,112954210168687+c.lower,112954598027853+c.upper)) = pointBounds55507 := by
 decide +kernel
def cuts55508 : List PrefixCut := [⟨64,221327434,221327559⟩]
theorem checked55508 : checkPrefixCuts (2^48) 7279476737 10 Manual.Count131072.C055508.packed 64 cuts55508 = true := by
 decide +kernel
def cuts55509 : List PrefixCut := [⟨9,32750245,32750263⟩,
⟨64,224146061,224146185⟩]
theorem checked55509 : checkPrefixCuts (2^48) 7279607809 10 Manual.Count131072.C055509.packed 64 cuts55509 = true := by
 decide +kernel
def pointBounds55509 : List (Nat × Nat × Nat) := [(7279626240,112954686776468,112955074635903)]
theorem point_links_checked55509 : (cuts55509.take 1).map (fun c => (7279607809-1+2*2^10*c.k,112954654026223+c.lower,112955041885640+c.upper)) = pointBounds55509 := by
 decide +kernel
def cuts55510 : List PrefixCut := [⟨57,198855176,198855288⟩,
⟨64,222750061,222750187⟩]
theorem checked55510 : checkPrefixCuts (2^48) 7279738881 10 Manual.Count131072.C055510.packed 64 cuts55510 = true := by
 decide +kernel
def pointBounds55510 : List (Nat × Nat × Nat) := [(7279855616,112955077027460,112955464887113)]
theorem point_links_checked55510 : (cuts55510.take 1).map (fun c => (7279738881-1+2*2^10*c.k,112954878172284+c.lower,112955266031825+c.upper)) = pointBounds55510 := by
 decide +kernel
def cuts55511 : List PrefixCut := [⟨64,223867312,223867437⟩]
theorem checked55511 : checkPrefixCuts (2^48) 7279869953 10 Manual.Count131072.C055511.packed 64 cuts55511 = true := by
 decide +kernel
def cuts55512 : List PrefixCut := [⟨41,143597735,143597814⟩,
⟨64,221620790,221620915⟩]
theorem checked55512 : checkPrefixCuts (2^48) 7280001025 10 Manual.Count131072.C055512.packed 64 cuts55512 = true := by
 decide +kernel
def pointBounds55512 : List (Nat × Nat × Nat) := [(7280084992,112955468387392,112955856247263)]
theorem point_links_checked55512 : (cuts55512.take 1).map (fun c => (7280001025-1+2*2^10*c.k,112955324789657+c.lower,112955712649449+c.upper)) = pointBounds55512 := by
 decide +kernel
def cuts55513 : List PrefixCut := [⟨64,222158095,222158219⟩]
theorem checked55513 : checkPrefixCuts (2^48) 7280132097 10 Manual.Count131072.C055513.packed 64 cuts55513 = true := by
 decide +kernel
def cuts55514 : List PrefixCut := [⟨25,88614680,88614731⟩,
⟨64,223623264,223623391⟩]
theorem checked55514 : checkPrefixCuts (2^48) 7280263169 10 Manual.Count131072.C055514.packed 64 cuts55514 = true := by
 decide +kernel
def pointBounds55514 : List (Nat × Nat × Nat) := [(7280314368,112955857183222,112956245043314)]
theorem point_links_checked55514 : (cuts55514.take 1).map (fun c => (7280263169-1+2*2^10*c.k,112955768568542+c.lower,112956156428583+c.upper)) = pointBounds55514 := by
 decide +kernel
def cuts55515 : List PrefixCut := [⟨64,222691341,222691470⟩]
theorem checked55515 : checkPrefixCuts (2^48) 7280394241 10 Manual.Count131072.C055515.packed 64 cuts55515 = true := by
 decide +kernel
def cuts55516 : List PrefixCut := [⟨9,32127536,32127552⟩,
⟨64,223808496,223808624⟩]
theorem checked55516 : checkPrefixCuts (2^48) 7280525313 10 Manual.Count131072.C055516.packed 64 cuts55516 = true := by
 decide +kernel
def pointBounds55516 : List (Nat × Nat × Nat) := [(7280543744,112956247010683,112956634870996)]
theorem point_links_checked55516 : (cuts55516.take 1).map (fun c => (7280525313-1+2*2^10*c.k,112956214883147+c.lower,112956602743444+c.upper)) = pointBounds55516 := by
 decide +kernel
def cuts55517 : List PrefixCut := [⟨57,197438356,197438467⟩,
⟨64,222142089,222142214⟩]
theorem checked55517 : checkPrefixCuts (2^48) 7280656385 10 Manual.Count131072.C055517.packed 64 cuts55517 = true := by
 decide +kernel
def pointBounds55517 : List (Nat × Nat × Nat) := [(7280773120,112956636129999,112957023990535)]
theorem point_links_checked55517 : (cuts55517.take 1).map (fun c => (7280656385-1+2*2^10*c.k,112956438691643+c.lower,112956826552068+c.upper)) = pointBounds55517 := by
 decide +kernel
def cuts55518 : List PrefixCut := [⟨64,224341690,224341814⟩]
theorem checked55518 : checkPrefixCuts (2^48) 7280787457 10 Manual.Count131072.C055518.packed 64 cuts55518 = true := by
 decide +kernel
def cuts55519 : List PrefixCut := [⟨41,142883786,142883868⟩,
⟨64,223255194,223255321⟩]
theorem checked55519 : checkPrefixCuts (2^48) 7280918529 10 Manual.Count131072.C055519.packed 64 cuts55519 = true := by
 decide +kernel
def pointBounds55519 : List (Nat × Nat × Nat) := [(7281002496,112957028059208,112957415919964)]
theorem point_links_checked55519 : (cuts55519.take 1).map (fun c => (7280918529-1+2*2^10*c.k,112956885175422+c.lower,112957273036096+c.upper)) = pointBounds55519 := by
 decide +kernel
def cuts55520 : List PrefixCut := [⟨64,221550213,221550337⟩]
theorem checked55520 : checkPrefixCuts (2^48) 7281049601 10 Manual.Count131072.C055520.packed 64 cuts55520 = true := by
 decide +kernel
def cuts55521 : List PrefixCut := [⟨25,87907673,87907724⟩,
⟨64,224252255,224252383⟩]
theorem checked55521 : checkPrefixCuts (2^48) 7281180673 10 Manual.Count131072.C055521.packed 64 cuts55521 = true := by
 decide +kernel
def pointBounds55521 : List (Nat × Nat × Nat) := [(7281231872,112957417888502,112957805749478)]
theorem point_links_checked55521 : (cuts55521.take 1).map (fun c => (7281180673-1+2*2^10*c.k,112957329980829+c.lower,112957717841754+c.upper)) = pointBounds55521 := by
 decide +kernel
def cuts55522 : List PrefixCut := [⟨64,222469993,222470121⟩]
theorem checked55522 : checkPrefixCuts (2^48) 7281311745 10 Manual.Count131072.C055522.packed 64 cuts55522 = true := by
 decide +kernel
def cuts55523 : List PrefixCut := [⟨9,31041108,31041126⟩,
⟨64,224244170,224244298⟩]
theorem checked55523 : checkPrefixCuts (2^48) 7281442817 10 Manual.Count131072.C055523.packed 64 cuts55523 = true := by
 decide +kernel
def pointBounds55523 : List (Nat × Nat × Nat) := [(7281461248,112957807744185,112958195605384)]
theorem point_links_checked55523 : (cuts55523.take 1).map (fun c => (7281442817-1+2*2^10*c.k,112957776703077+c.lower,112958164564258+c.upper)) = pointBounds55523 := by
 decide +kernel
def cuts55524 : List PrefixCut := [⟨57,198766411,198766523⟩,
⟨64,224008203,224008329⟩]
theorem checked55524 : checkPrefixCuts (2^48) 7281573889 10 Manual.Count131072.C055524.packed 64 cuts55524 = true := by
 decide +kernel
def pointBounds55524 : List (Nat × Nat × Nat) := [(7281690624,112958199713658,112958587575079)]
theorem point_links_checked55524 : (cuts55524.take 1).map (fun c => (7281573889-1+2*2^10*c.k,112958000947247+c.lower,112958388808556+c.upper)) = pointBounds55524 := by
 decide +kernel
def cuts55525 : List PrefixCut := [⟨64,222148756,222148883⟩]
theorem checked55525 : checkPrefixCuts (2^48) 7281704961 10 Manual.Count131072.C055525.packed 64 cuts55525 = true := by
 decide +kernel
def cuts55526 : List PrefixCut := [⟨41,141512889,141512969⟩,
⟨64,219902829,219902954⟩]
theorem checked55526 : checkPrefixCuts (2^48) 7281836033 10 Manual.Count131072.C055526.packed 64 cuts55526 = true := by
 decide +kernel
def pointBounds55526 : List (Nat × Nat × Nat) := [(7281920000,112958588617095,112958976478737)]
theorem point_links_checked55526 : (cuts55526.take 1).map (fun c => (7281836033-1+2*2^10*c.k,112958447104206+c.lower,112958834965768+c.upper)) = pointBounds55526 := by
 decide +kernel
def cuts55527 : List PrefixCut := [⟨64,223493597,223493725⟩]
theorem checked55527 : checkPrefixCuts (2^48) 7281967105 10 Manual.Count131072.C055527.packed 64 cuts55527 = true := by
 decide +kernel
def cuts55528 : List PrefixCut := [⟨25,87432763,87432813⟩,
⟨64,222755200,222755324⟩]
theorem checked55528 : checkPrefixCuts (2^48) 7282098177 10 Manual.Count131072.C055528.packed 64 cuts55528 = true := by
 decide +kernel
def pointBounds55528 : List (Nat × Nat × Nat) := [(7282149376,112958977933395,112959365795260)]
theorem point_links_checked55528 : (cuts55528.take 1).map (fun c => (7282098177-1+2*2^10*c.k,112958890500632+c.lower,112959278362447+c.upper)) = pointBounds55528 := by
 decide +kernel
def cuts55529 : List PrefixCut := [⟨64,222789834,222789962⟩]
theorem checked55529 : checkPrefixCuts (2^48) 7282229249 10 Manual.Count131072.C055529.packed 64 cuts55529 = true := by
 decide +kernel
def cuts55530 : List PrefixCut := [⟨9,31114501,31114518⟩,
⟨64,222128752,222128877⟩]
theorem checked55530 : checkPrefixCuts (2^48) 7282360321 10 Manual.Count131072.C055530.packed 64 cuts55530 = true := by
 decide +kernel
def pointBounds55530 : List (Nat × Nat × Nat) := [(7282378752,112959367160167,112959755022251)]
theorem point_links_checked55530 : (cuts55530.take 1).map (fun c => (7282360321-1+2*2^10*c.k,112959336045666+c.lower,112959723907733+c.upper)) = pointBounds55530 := by
 decide +kernel
def cuts55531 : List PrefixCut := [⟨57,196538279,196538392⟩,
⟨64,221158488,221158614⟩]
theorem checked55531 : checkPrefixCuts (2^48) 7282491393 10 Manual.Count131072.C055531.packed 64 cuts55531 = true := by
 decide +kernel
def pointBounds55531 : List (Nat × Nat × Nat) := [(7282608128,112959754712697,112960142575002)]
theorem point_links_checked55531 : (cuts55531.take 1).map (fun c => (7282491393-1+2*2^10*c.k,112959558174418+c.lower,112959946036610+c.upper)) = pointBounds55531 := by
 decide +kernel
def cuts55532 : List PrefixCut := [⟨64,225328702,225328827⟩]
theorem checked55532 : checkPrefixCuts (2^48) 7282622465 10 Manual.Count131072.C055532.packed 64 cuts55532 = true := by
 decide +kernel
def cuts55533 : List PrefixCut := [⟨41,140335594,140335672⟩,
⟨64,221846222,221846344⟩]
theorem checked55533 : checkPrefixCuts (2^48) 7282753537 10 Manual.Count131072.C055533.packed 64 cuts55533 = true := by
 decide +kernel
def pointBounds55533 : List (Nat × Nat × Nat) := [(7282837504,112960144997202,112960532859723)]
theorem point_links_checked55533 : (cuts55533.take 1).map (fun c => (7282753537-1+2*2^10*c.k,112960004661608+c.lower,112960392524051+c.upper)) = pointBounds55533 := by
 decide +kernel
def cuts55534 : List PrefixCut := [⟨64,221958171,221958301⟩]
theorem checked55534 : checkPrefixCuts (2^48) 7282884609 10 Manual.Count131072.C055534.packed 64 cuts55534 = true := by
 decide +kernel
def cuts55535 : List PrefixCut := [⟨25,87305810,87305860⟩,
⟨64,224930059,224930189⟩]
theorem checked55535 : checkPrefixCuts (2^48) 7283015681 10 Manual.Count131072.C055535.packed 64 cuts55535 = true := by
 decide +kernel
def pointBounds55535 : List (Nat × Nat × Nat) := [(7283066880,112960535771811,112960923634556)]
theorem point_links_checked55535 : (cuts55535.take 1).map (fun c => (7283015681-1+2*2^10*c.k,112960448466001+c.lower,112960836328696+c.upper)) = pointBounds55535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000172
