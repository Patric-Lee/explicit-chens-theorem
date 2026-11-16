import PlattAssemblyKernel
import PlattCertificates.Count131072.C048512
import PlattCertificates.Count131072.C048513
import PlattCertificates.Count131072.C048514
import PlattCertificates.Count131072.C048515
import PlattCertificates.Count131072.C048516
import PlattCertificates.Count131072.C048517
import PlattCertificates.Count131072.C048518
import PlattCertificates.Count131072.C048519
import PlattCertificates.Count131072.C048520
import PlattCertificates.Count131072.C048521
import PlattCertificates.Count131072.C048522
import PlattCertificates.Count131072.C048523
import PlattCertificates.Count131072.C048524
import PlattCertificates.Count131072.C048525
import PlattCertificates.Count131072.C048526
import PlattCertificates.Count131072.C048527
import PlattCertificates.Count131072.C048528
import PlattCertificates.Count131072.C048529
import PlattCertificates.Count131072.C048530
import PlattCertificates.Count131072.C048531
import PlattCertificates.Count131072.C048532
import PlattCertificates.Count131072.C048533
import PlattCertificates.Count131072.C048534
import PlattCertificates.Count131072.C048535
import PlattCertificates.Count131072.C048536
import PlattCertificates.Count131072.C048537
import PlattCertificates.Count131072.C048538
import PlattCertificates.Count131072.C048539
import PlattCertificates.Count131072.C048540
import PlattCertificates.Count131072.C048541
import PlattCertificates.Count131072.C048542
import PlattCertificates.Count131072.C048543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48512 : List PrefixCut := [⟨48,192352689,192352798⟩,
⟨64,256631800,256631946⟩]
theorem checked48512 : checkPrefixCuts (2^48) 6362497025 10 Manual.Count131072.C048512.packed 64 cuts48512 = true := by
 decide +kernel
def pointBounds48512 : List (Nat × Nat × Nat) := [(6362595328,111280825894633,111281212802175)]
theorem point_links_checked48512 : (cuts48512.take 1).map (fun c => (6362497025-1+2*2^10*c.k,111280633541944+c.lower,111281020449377+c.upper)) = pointBounds48512 := by
 decide +kernel
def cuts48513 : List PrefixCut := [⟨64,256316837,256316978⟩]
theorem checked48513 : checkPrefixCuts (2^48) 6362628097 10 Manual.Count131072.C048513.packed 64 cuts48513 = true := by
 decide +kernel
def cuts48514 : List PrefixCut := [⟨18,72992268,72992311⟩,
⟨64,259142756,259142902⟩]
theorem checked48514 : checkPrefixCuts (2^48) 6362759169 10 Manual.Count131072.C048514.packed 64 cuts48514 = true := by
 decide +kernel
def pointBounds48514 : List (Nat × Nat × Nat) := [(6362796032,111281219482849,111281606390612)]
theorem point_links_checked48514 : (cuts48514.take 1).map (fun c => (6362759169-1+2*2^10*c.k,111281146490581+c.lower,111281533398301+c.upper)) = pointBounds48514 := by
 decide +kernel
def cuts48515 : List PrefixCut := [⟨52,208221602,208221722⟩,
⟨64,256881346,256881492⟩]
theorem checked48515 : checkPrefixCuts (2^48) 6362890241 10 Manual.Count131072.C048515.packed 64 cuts48515 = true := by
 decide +kernel
def pointBounds48515 : List (Nat × Nat × Nat) := [(6362996736,111281613854939,111282000762925)]
theorem point_links_checked48515 : (cuts48515.take 1).map (fun c => (6362890241-1+2*2^10*c.k,111281405633337+c.lower,111281792541203+c.upper)) = pointBounds48515 := by
 decide +kernel
def cuts48516 : List PrefixCut := [⟨64,256787621,256787765⟩]
theorem checked48516 : checkPrefixCuts (2^48) 6363021313 10 Manual.Count131072.C048516.packed 64 cuts48516 = true := by
 decide +kernel
def cuts48517 : List PrefixCut := [⟨22,89133479,89133528⟩,
⟨64,257224656,257224804⟩]
theorem checked48517 : checkPrefixCuts (2^48) 6363152385 10 Manual.Count131072.C048517.packed 64 cuts48517 = true := by
 decide +kernel
def pointBounds48517 : List (Nat × Nat × Nat) := [(6363197440,111282008435783,111282395343988)]
theorem point_links_checked48517 : (cuts48517.take 1).map (fun c => (6363152385-1+2*2^10*c.k,111281919302304+c.lower,111282306210460+c.upper)) = pointBounds48517 := by
 decide +kernel
def cuts48518 : List PrefixCut := [⟨56,223955838,223955970⟩,
⟨64,256688531,256688680⟩]
theorem checked48518 : checkPrefixCuts (2^48) 6363283457 10 Manual.Count131072.C048518.packed 64 cuts48518 = true := by
 decide +kernel
def pointBounds48518 : List (Nat × Nat × Nat) := [(6363398144,111282400482798,111282787391234)]
theorem point_links_checked48518 : (cuts48518.take 1).map (fun c => (6363283457-1+2*2^10*c.k,111282176526960+c.lower,111282563435264+c.upper)) = pointBounds48518 := by
 decide +kernel
def cuts48519 : List PrefixCut := [⟨64,259735323,259735476⟩]
theorem checked48519 : checkPrefixCuts (2^48) 6363414529 10 Manual.Count131072.C048519.packed 64 cuts48519 = true := by
 decide +kernel
def cuts48520 : List PrefixCut := [⟨26,104741886,104741944⟩,
⟨64,257253004,257253148⟩]
theorem checked48520 : checkPrefixCuts (2^48) 6363545601 10 Manual.Count131072.C048520.packed 64 cuts48520 = true := by
 decide +kernel
def pointBounds48520 : List (Nat × Nat × Nat) := [(6363598848,111282797692700,111283184601364)]
theorem point_links_checked48520 : (cuts48520.take 1).map (fun c => (6363545601-1+2*2^10*c.k,111282692950814+c.lower,111283079859420+c.upper)) = pointBounds48520 := by
 decide +kernel
def cuts48521 : List PrefixCut := [⟨60,238980443,238980588⟩,
⟨64,256009228,256009381⟩]
theorem checked48521 : checkPrefixCuts (2^48) 6363676673 10 Manual.Count131072.C048521.packed 64 cuts48521 = true := by
 decide +kernel
def pointBounds48521 : List (Nat × Nat × Nat) := [(6363799552,111283189184261,111283576093156)]
theorem point_links_checked48521 : (cuts48521.take 1).map (fun c => (6363676673-1+2*2^10*c.k,111282950203818+c.lower,111283337112568+c.upper)) = pointBounds48521 := by
 decide +kernel
def cuts48522 : List PrefixCut := [⟨64,256225097,256225244⟩]
theorem checked48522 : checkPrefixCuts (2^48) 6363807745 10 Manual.Count131072.C048522.packed 64 cuts48522 = true := by
 decide +kernel
def cuts48523 : List PrefixCut := [⟨30,120613721,120613793⟩,
⟨64,258696646,258696796⟩]
theorem checked48523 : checkPrefixCuts (2^48) 6363938817 10 Manual.Count131072.C048523.packed 64 cuts48523 = true := by
 decide +kernel
def pointBounds48523 : List (Nat × Nat × Nat) := [(6364000256,111283583051864,111283969960986)]
theorem point_links_checked48523 : (cuts48523.take 1).map (fun c => (6363938817-1+2*2^10*c.k,111283462438143+c.lower,111283849347193+c.upper)) = pointBounds48523 := by
 decide +kernel
def cuts48524 : List PrefixCut := [⟨64,256081865,256082013⟩]
theorem checked48524 : checkPrefixCuts (2^48) 6364069889 10 Manual.Count131072.C048524.packed 64 cuts48524 = true := by
 decide +kernel
def pointBounds48524 : List (Nat × Nat × Nat) := [(6364200960,111283977216654,111284364126002)]
theorem point_links_checked48524 : (cuts48524.take 1).map (fun c => (6364069889-1+2*2^10*c.k,111283721134789+c.lower,111284108043989+c.upper)) = pointBounds48524 := by
 decide +kernel
def cuts48525 : List PrefixCut := [⟨64,258641772,258641927⟩]
theorem checked48525 : checkPrefixCuts (2^48) 6364200961 10 Manual.Count131072.C048525.packed 64 cuts48525 = true := by
 decide +kernel
def cuts48526 : List PrefixCut := [⟨34,135156772,135156855⟩,
⟨64,254523387,254523535⟩]
theorem checked48526 : checkPrefixCuts (2^48) 6364332033 10 Manual.Count131072.C048526.packed 64 cuts48526 = true := by
 decide +kernel
def pointBounds48526 : List (Nat × Nat × Nat) := [(6364401664,111284371015198,111284757924784)]
theorem point_links_checked48526 : (cuts48526.take 1).map (fun c => (6364332033-1+2*2^10*c.k,111284235858426+c.lower,111284622767929+c.upper)) = pointBounds48526 := by
 decide +kernel
def cuts48527 : List PrefixCut := [⟨64,255579544,255579687⟩]
theorem checked48527 : checkPrefixCuts (2^48) 6364463105 10 Manual.Count131072.C048527.packed 64 cuts48527 = true := by
 decide +kernel
def cuts48528 : List PrefixCut := [⟨4,16495958,16495966⟩,
⟨64,254734047,254734188⟩]
theorem checked48528 : checkPrefixCuts (2^48) 6364594177 10 Manual.Count131072.C048528.packed 64 cuts48528 = true := by
 decide +kernel
def pointBounds48528 : List (Nat × Nat × Nat) := [(6364602368,111284762457315,111285149367117)]
theorem point_links_checked48528 : (cuts48528.take 1).map (fun c => (6364594177-1+2*2^10*c.k,111284745961357+c.lower,111285132871151+c.upper)) = pointBounds48528 := by
 decide +kernel
def cuts48529 : List PrefixCut := [⟨38,155800914,155801005⟩,
⟨64,260787451,260787602⟩]
theorem checked48529 : checkPrefixCuts (2^48) 6364725249 10 Manual.Count131072.C048529.packed 64 cuts48529 = true := by
 decide +kernel
def pointBounds48529 : List (Nat × Nat × Nat) := [(6364803072,111285156496318,111285543406344)]
theorem point_links_checked48529 : (cuts48529.take 1).map (fun c => (6364725249-1+2*2^10*c.k,111285000695404+c.lower,111285387605339+c.upper)) = pointBounds48529 := by
 decide +kernel
def cuts48530 : List PrefixCut := [⟨64,254148630,254148778⟩]
theorem checked48530 : checkPrefixCuts (2^48) 6364856321 10 Manual.Count131072.C048530.packed 64 cuts48530 = true := by
 decide +kernel
def cuts48531 : List PrefixCut := [⟨8,32061184,32061203⟩,
⟨64,255735397,255735547⟩]
theorem checked48531 : checkPrefixCuts (2^48) 6364987393 10 Manual.Count131072.C048531.packed 64 cuts48531 = true := by
 decide +kernel
def pointBounds48531 : List (Nat × Nat × Nat) := [(6365003776,111285547692669,111285934602922)]
theorem point_links_checked48531 : (cuts48531.take 1).map (fun c => (6364987393-1+2*2^10*c.k,111285515631485+c.lower,111285902541719+c.upper)) = pointBounds48531 := by
 decide +kernel
def cuts48532 : List PrefixCut := [⟨42,168615335,168615426⟩,
⟨64,260329098,260329244⟩]
theorem checked48532 : checkPrefixCuts (2^48) 6365118465 10 Manual.Count131072.C048532.packed 64 cuts48532 = true := by
 decide +kernel
def pointBounds48532 : List (Nat × Nat × Nat) := [(6365204480,111285939982217,111286326892692)]
theorem point_links_checked48532 : (cuts48532.take 1).map (fun c => (6365118465-1+2*2^10*c.k,111285771366882+c.lower,111286158277266+c.upper)) = pointBounds48532 := by
 decide +kernel
def cuts48533 : List PrefixCut := [⟨64,252894786,252894933⟩]
theorem checked48533 : checkPrefixCuts (2^48) 6365249537 10 Manual.Count131072.C048533.packed 64 cuts48533 = true := by
 decide +kernel
def cuts48534 : List PrefixCut := [⟨12,48641522,48641547⟩,
⟨64,257797901,257798046⟩]
theorem checked48534 : checkPrefixCuts (2^48) 6365380609 10 Manual.Count131072.C048534.packed 64 cuts48534 = true := by
 decide +kernel
def pointBounds48534 : List (Nat × Nat × Nat) := [(6365405184,111286333232288,111286720142990)]
theorem point_links_checked48534 : (cuts48534.take 1).map (fun c => (6365380609-1+2*2^10*c.k,111286284590766+c.lower,111286671501443+c.upper)) = pointBounds48534 := by
 decide +kernel
def cuts48535 : List PrefixCut := [⟨46,185496245,185496353⟩,
⟨64,256731369,256731518⟩]
theorem checked48535 : checkPrefixCuts (2^48) 6365511681 10 Manual.Count131072.C048535.packed 64 cuts48535 = true := by
 decide +kernel
def pointBounds48535 : List (Nat × Nat × Nat) := [(6365605888,111286727884912,111287114795842)]
theorem point_links_checked48535 : (cuts48535.take 1).map (fun c => (6365511681-1+2*2^10*c.k,111286542388667+c.lower,111286929299489+c.upper)) = pointBounds48535 := by
 decide +kernel
def cuts48536 : List PrefixCut := [⟨64,253675075,253675214⟩]
theorem checked48536 : checkPrefixCuts (2^48) 6365642753 10 Manual.Count131072.C048536.packed 64 cuts48536 = true := by
 decide +kernel
def cuts48537 : List PrefixCut := [⟨16,63097378,63097413⟩,
⟨64,252829724,252829869⟩]
theorem checked48537 : checkPrefixCuts (2^48) 6365773825 10 Manual.Count131072.C048537.packed 64 cuts48537 = true := by
 decide +kernel
def pointBounds48537 : List (Nat × Nat × Nat) := [(6365806592,111287115892489,111287502803634)]
theorem point_links_checked48537 : (cuts48537.take 1).map (fun c => (6365773825-1+2*2^10*c.k,111287052795111+c.lower,111287439706221+c.upper)) = pointBounds48537 := by
 decide +kernel
def cuts48538 : List PrefixCut := [⟨50,198881988,198882105⟩,
⟨64,254327842,254327993⟩]
theorem checked48538 : checkPrefixCuts (2^48) 6365904897 10 Manual.Count131072.C048538.packed 64 cuts48538 = true := by
 decide +kernel
def pointBounds48538 : List (Nat × Nat × Nat) := [(6366007296,111287504506823,111287891418195)]
theorem point_links_checked48538 : (cuts48538.take 1).map (fun c => (6365904897-1+2*2^10*c.k,111287305624835+c.lower,111287692536090+c.upper)) = pointBounds48538 := by
 decide +kernel
def cuts48539 : List PrefixCut := [⟨64,256400719,256400866⟩]
theorem checked48539 : checkPrefixCuts (2^48) 6366035969 10 Manual.Count131072.C048539.packed 64 cuts48539 = true := by
 decide +kernel
def cuts48540 : List PrefixCut := [⟨20,80734841,80734886⟩,
⟨64,255643798,255643945⟩]
theorem checked48540 : checkPrefixCuts (2^48) 6366167041 10 Manual.Count131072.C048540.packed 64 cuts48540 = true := by
 decide +kernel
def pointBounds48540 : List (Nat × Nat × Nat) := [(6366208000,111287897088237,111288283999835)]
theorem point_links_checked48540 : (cuts48540.take 1).map (fun c => (6366167041-1+2*2^10*c.k,111287816353396+c.lower,111288203264949+c.upper)) = pointBounds48540 := by
 decide +kernel
def cuts48541 : List PrefixCut := [⟨54,218057990,218058112⟩,
⟨64,257495484,257495629⟩]
theorem checked48541 : checkPrefixCuts (2^48) 6366298113 10 Manual.Count131072.C048541.packed 64 cuts48541 = true := by
 decide +kernel
def pointBounds48541 : List (Nat × Nat × Nat) := [(6366408704,111288290055184,111288676967006)]
theorem point_links_checked48541 : (cuts48541.take 1).map (fun c => (6366298113-1+2*2^10*c.k,111288071997194+c.lower,111288458908894+c.upper)) = pointBounds48541 := by
 decide +kernel
def cuts48542 : List PrefixCut := [⟨64,259745009,259745155⟩]
theorem checked48542 : checkPrefixCuts (2^48) 6366429185 10 Manual.Count131072.C048542.packed 64 cuts48542 = true := by
 decide +kernel
def cuts48543 : List PrefixCut := [⟨24,95540581,95540637⟩,
⟨64,255141676,255141824⟩]
theorem checked48543 : checkPrefixCuts (2^48) 6366560257 10 Manual.Count131072.C048543.packed 64 cuts48543 = true := by
 decide +kernel
def pointBounds48543 : List (Nat × Nat × Nat) := [(6366609408,111288684778268,111289071690315)]
theorem point_links_checked48543 : (cuts48543.take 1).map (fun c => (6366560257-1+2*2^10*c.k,111288589237687+c.lower,111288976149678+c.upper)) = pointBounds48543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000266
