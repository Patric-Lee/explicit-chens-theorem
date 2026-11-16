import PlattAssemblyKernel
import PlattCertificates.Count131072.C055536
import PlattCertificates.Count131072.C055537
import PlattCertificates.Count131072.C055538
import PlattCertificates.Count131072.C055539
import PlattCertificates.Count131072.C055540
import PlattCertificates.Count131072.C055541
import PlattCertificates.Count131072.C055542
import PlattCertificates.Count131072.C055543
import PlattCertificates.Count131072.C055544
import PlattCertificates.Count131072.C055545
import PlattCertificates.Count131072.C055546
import PlattCertificates.Count131072.C055547
import PlattCertificates.Count131072.C055548
import PlattCertificates.Count131072.C055549
import PlattCertificates.Count131072.C055550
import PlattCertificates.Count131072.C055551
import PlattCertificates.Count131072.C055552
import PlattCertificates.Count131072.C055553
import PlattCertificates.Count131072.C055554
import PlattCertificates.Count131072.C055555
import PlattCertificates.Count131072.C055556
import PlattCertificates.Count131072.C055557
import PlattCertificates.Count131072.C055558
import PlattCertificates.Count131072.C055559
import PlattCertificates.Count131072.C055560
import PlattCertificates.Count131072.C055561
import PlattCertificates.Count131072.C055562
import PlattCertificates.Count131072.C055563
import PlattCertificates.Count131072.C055564
import PlattCertificates.Count131072.C055565
import PlattCertificates.Count131072.C055566
import PlattCertificates.Count131072.C055567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55536 : List PrefixCut := [⟨64,223032318,223032447⟩]
theorem checked55536 : checkPrefixCuts (2^48) 7283146753 10 Manual.Count131072.C055536.packed 64 cuts55536 = true := by
 decide +kernel
def cuts55537 : List PrefixCut := [⟨9,30801409,30801427⟩,
⟨64,222564531,222564659⟩]
theorem checked55537 : checkPrefixCuts (2^48) 7283277825 10 Manual.Count131072.C055537.packed 64 cuts55537 = true := by
 decide +kernel
def pointBounds55537 : List (Nat × Nat × Nat) := [(7283296256,112960927229787,112961315092759)]
theorem point_links_checked55537 : (cuts55537.take 1).map (fun c => (7283277825-1+2*2^10*c.k,112960896428378+c.lower,112961284291332+c.upper)) = pointBounds55537 := by
 decide +kernel
def cuts55538 : List PrefixCut := [⟨57,197595608,197595723⟩,
⟨64,221671681,221671810⟩]
theorem checked55538 : checkPrefixCuts (2^48) 7283408897 10 Manual.Count131072.C055538.packed 64 cuts55538 = true := by
 decide +kernel
def pointBounds55538 : List (Nat × Nat × Nat) := [(7283525632,112961316588517,112961704451714)]
theorem point_links_checked55538 : (cuts55538.take 1).map (fun c => (7283408897-1+2*2^10*c.k,112961118992909+c.lower,112961506855991+c.upper)) = pointBounds55538 := by
 decide +kernel
def cuts55539 : List PrefixCut := [⟨64,223599936,223600062⟩]
theorem checked55539 : checkPrefixCuts (2^48) 7283539969 10 Manual.Count131072.C055539.packed 64 cuts55539 = true := by
 decide +kernel
def cuts55540 : List PrefixCut := [⟨41,140781629,140781710⟩,
⟨64,221818260,221818386⟩]
theorem checked55540 : checkPrefixCuts (2^48) 7283671041 10 Manual.Count131072.C055540.packed 64 cuts55540 = true := by
 decide +kernel
def pointBounds55540 : List (Nat × Nat × Nat) := [(7283755008,112961705046155,112962092909573)]
theorem point_links_checked55540 : (cuts55540.take 1).map (fun c => (7283671041-1+2*2^10*c.k,112961564264526+c.lower,112961952127863+c.upper)) = pointBounds55540 := by
 decide +kernel
def cuts55541 : List PrefixCut := [⟨64,222548506,222548634⟩]
theorem checked55541 : checkPrefixCuts (2^48) 7283802113 10 Manual.Count131072.C055541.packed 64 cuts55541 = true := by
 decide +kernel
def cuts55542 : List PrefixCut := [⟨25,85826372,85826422⟩,
⟨64,221501153,221501280⟩]
theorem checked55542 : checkPrefixCuts (2^48) 7283933185 10 Manual.Count131072.C055542.packed 64 cuts55542 = true := by
 decide +kernel
def pointBounds55542 : List (Nat × Nat × Nat) := [(7283984384,112962094457664,112962482321305)]
theorem point_links_checked55542 : (cuts55542.take 1).map (fun c => (7283933185-1+2*2^10*c.k,112962008631292+c.lower,112962396494883+c.upper)) = pointBounds55542 := by
 decide +kernel
def cuts55543 : List PrefixCut := [⟨64,225090897,225091023⟩]
theorem checked55543 : checkPrefixCuts (2^48) 7284064257 10 Manual.Count131072.C055543.packed 64 cuts55543 = true := by
 decide +kernel
def cuts55544 : List PrefixCut := [⟨9,30642960,30642978⟩,
⟨64,223193403,223193530⟩]
theorem checked55544 : checkPrefixCuts (2^48) 7284195329 10 Manual.Count131072.C055544.packed 64 cuts55544 = true := by
 decide +kernel
def pointBounds55544 : List (Nat × Nat × Nat) := [(7284213760,112962485866302,112962873730164)]
theorem point_links_checked55544 : (cuts55544.take 1).map (fun c => (7284195329-1+2*2^10*c.k,112962455223342+c.lower,112962843087186+c.upper)) = pointBounds55544 := by
 decide +kernel
def cuts55545 : List PrefixCut := [⟨57,195600045,195600159⟩,
⟨64,219325321,219325448⟩]
theorem checked55545 : checkPrefixCuts (2^48) 7284326401 10 Manual.Count131072.C055545.packed 64 cuts55545 = true := by
 decide +kernel
def pointBounds55545 : List (Nat × Nat × Nat) := [(7284443136,112962874016790,112963261880875)]
theorem point_links_checked55545 : (cuts55545.take 1).map (fun c => (7284326401-1+2*2^10*c.k,112962678416745+c.lower,112963066280716+c.upper)) = pointBounds55545 := by
 decide +kernel
def cuts55546 : List PrefixCut := [⟨64,221060164,221060288⟩]
theorem checked55546 : checkPrefixCuts (2^48) 7284457473 10 Manual.Count131072.C055546.packed 64 cuts55546 = true := by
 decide +kernel
def cuts55547 : List PrefixCut := [⟨41,140841184,140841265⟩,
⟨64,221558489,221558615⟩]
theorem checked55547 : checkPrefixCuts (2^48) 7284588545 10 Manual.Count131072.C055547.packed 64 cuts55547 = true := by
 decide +kernel
def pointBounds55547 : List (Nat × Nat × Nat) := [(7284672512,112963259643414,112963647507717)]
theorem point_links_checked55547 : (cuts55547.take 1).map (fun c => (7284588545-1+2*2^10*c.k,112963118802230+c.lower,112963506666452+c.upper)) = pointBounds55547 := by
 decide +kernel
def cuts55548 : List PrefixCut := [⟨64,222829602,222829731⟩]
theorem checked55548 : checkPrefixCuts (2^48) 7284719617 10 Manual.Count131072.C055548.packed 64 cuts55548 = true := by
 decide +kernel
def cuts55549 : List PrefixCut := [⟨25,85081433,85081482⟩,
⟨64,221898253,221898380⟩]
theorem checked55549 : checkPrefixCuts (2^48) 7284850689 10 Manual.Count131072.C055549.packed 64 cuts55549 = true := by
 decide +kernel
def pointBounds55549 : List (Nat × Nat × Nat) := [(7284901888,112963648271754,112964036136280)]
theorem point_links_checked55549 : (cuts55549.take 1).map (fun c => (7284850689-1+2*2^10*c.k,112963563190321+c.lower,112963951054798+c.upper)) = pointBounds55549 := by
 decide +kernel
def cuts55550 : List PrefixCut := [⟨64,218378284,218378409⟩]
theorem checked55550 : checkPrefixCuts (2^48) 7284981761 10 Manual.Count131072.C055550.packed 64 cuts55550 = true := by
 decide +kernel
def cuts55551 : List PrefixCut := [⟨9,31527751,31527769⟩,
⟨64,223590299,223590427⟩]
theorem checked55551 : checkPrefixCuts (2^48) 7285112833 10 Manual.Count131072.C055551.packed 64 cuts55551 = true := by
 decide +kernel
def pointBounds55551 : List (Nat × Nat × Nat) := [(7285131264,112964034994609,112964422859356)]
theorem point_links_checked55551 : (cuts55551.take 1).map (fun c => (7285112833-1+2*2^10*c.k,112964003466858+c.lower,112964391331587+c.upper)) = pointBounds55551 := by
 decide +kernel
def cuts55552 : List PrefixCut := [⟨57,198125374,198125488⟩,
⟨64,222968096,222968223⟩]
theorem checked55552 : checkPrefixCuts (2^48) 7285243905 10 Manual.Count131072.C055552.packed 64 cuts55552 = true := by
 decide +kernel
def pointBounds55552 : List (Nat × Nat × Nat) := [(7285360640,112964425182531,112964813047502)]
theorem point_links_checked55552 : (cuts55552.take 1).map (fun c => (7285243905-1+2*2^10*c.k,112964227057157+c.lower,112964614922014+c.upper)) = pointBounds55552 := by
 decide +kernel
def cuts55553 : List PrefixCut := [⟨64,223968616,223968741⟩]
theorem checked55553 : checkPrefixCuts (2^48) 7285374977 10 Manual.Count131072.C055553.packed 64 cuts55553 = true := by
 decide +kernel
def cuts55554 : List PrefixCut := [⟨41,142523382,142523467⟩,
⟨64,221144268,221144400⟩]
theorem checked55554 : checkPrefixCuts (2^48) 7285506049 10 Manual.Count131072.C055554.packed 64 cuts55554 = true := by
 decide +kernel
def pointBounds55554 : List (Nat × Nat × Nat) := [(7285590016,112964816517251,112965204382445)]
theorem point_links_checked55554 : (cuts55554.take 1).map (fun c => (7285506049-1+2*2^10*c.k,112964673993869+c.lower,112965061858978+c.upper)) = pointBounds55554 := by
 decide +kernel
def cuts55555 : List PrefixCut := [⟨64,224037817,224037943⟩]
theorem checked55555 : checkPrefixCuts (2^48) 7285637121 10 Manual.Count131072.C055555.packed 64 cuts55555 = true := by
 decide +kernel
def cuts55556 : List PrefixCut := [⟨25,85534317,85534365⟩,
⟨64,225347293,225347420⟩]
theorem checked55556 : checkPrefixCuts (2^48) 7285768193 10 Manual.Count131072.C055556.packed 64 cuts55556 = true := by
 decide +kernel
def pointBounds55556 : List (Nat × Nat × Nat) := [(7285819392,112965204710271,112965592575686)]
theorem point_links_checked55556 : (cuts55556.take 1).map (fun c => (7285768193-1+2*2^10*c.k,112965119175954+c.lower,112965507041321+c.upper)) = pointBounds55556 := by
 decide +kernel
def cuts55557 : List PrefixCut := [⟨64,224531994,224532121⟩]
theorem checked55557 : checkPrefixCuts (2^48) 7285899265 10 Manual.Count131072.C055557.packed 64 cuts55557 = true := by
 decide +kernel
def cuts55558 : List PrefixCut := [⟨9,30673876,30673894⟩,
⟨64,224180248,224180376⟩]
theorem checked55558 : checkPrefixCuts (2^48) 7286030337 10 Manual.Count131072.C055558.packed 64 cuts55558 = true := by
 decide +kernel
def pointBounds55558 : List (Nat × Nat × Nat) := [(7286048768,112965599729117,112965987594756)]
theorem point_links_checked55558 : (cuts55558.take 1).map (fun c => (7286030337-1+2*2^10*c.k,112965569055241+c.lower,112965956920862+c.upper)) = pointBounds55558 := by
 decide +kernel
def cuts55559 : List PrefixCut := [⟨57,201886267,201886382⟩,
⟨64,226455444,226455573⟩]
theorem checked55559 : checkPrefixCuts (2^48) 7286161409 10 Manual.Count131072.C055559.packed 64 cuts55559 = true := by
 decide +kernel
def pointBounds55559 : List (Nat × Nat × Nat) := [(7286278144,112965995121756,112966382987620)]
theorem point_links_checked55559 : (cuts55559.take 1).map (fun c => (7286161409-1+2*2^10*c.k,112965793235489+c.lower,112966181101238+c.upper)) = pointBounds55559 := by
 decide +kernel
def cuts55560 : List PrefixCut := [⟨64,225678781,225678909⟩]
theorem checked55560 : checkPrefixCuts (2^48) 7286292481 10 Manual.Count131072.C055560.packed 64 cuts55560 = true := by
 decide +kernel
def cuts55561 : List PrefixCut := [⟨41,141230645,141230727⟩,
⟨64,221193670,221193796⟩]
theorem checked55561 : checkPrefixCuts (2^48) 7286423553 10 Manual.Count131072.C055561.packed 64 cuts55561 = true := by
 decide +kernel
def pointBounds55561 : List (Nat × Nat × Nat) := [(7286507520,112966386600359,112966774466447)]
theorem point_links_checked55561 : (cuts55561.take 1).map (fun c => (7286423553-1+2*2^10*c.k,112966245369714+c.lower,112966633235720+c.upper)) = pointBounds55561 := by
 decide +kernel
def cuts55562 : List PrefixCut := [⟨64,223816464,223816592⟩]
theorem checked55562 : checkPrefixCuts (2^48) 7286554625 10 Manual.Count131072.C055562.packed 64 cuts55562 = true := by
 decide +kernel
def cuts55563 : List PrefixCut := [⟨25,87184574,87184621⟩,
⟨64,224237336,224237463⟩]
theorem checked55563 : checkPrefixCuts (2^48) 7286685697 10 Manual.Count131072.C055563.packed 64 cuts55563 = true := by
 decide +kernel
def pointBounds55563 : List (Nat × Nat × Nat) := [(7286736896,112966777564422,112967165430729)]
theorem point_links_checked55563 : (cuts55563.take 1).map (fun c => (7286685697-1+2*2^10*c.k,112966690379848+c.lower,112967078246108+c.upper)) = pointBounds55563 := by
 decide +kernel
def cuts55564 : List PrefixCut := [⟨64,221683885,221684012⟩]
theorem checked55564 : checkPrefixCuts (2^48) 7286816769 10 Manual.Count131072.C055564.packed 64 cuts55564 = true := by
 decide +kernel
def cuts55565 : List PrefixCut := [⟨9,30747266,30747284⟩,
⟨64,224267896,224268022⟩]
theorem checked55565 : checkPrefixCuts (2^48) 7286947841 10 Manual.Count131072.C055565.packed 64 cuts55565 = true := by
 decide +kernel
def pointBounds55565 : List (Nat × Nat × Nat) := [(7286966272,112967167048335,112967554914867)]
theorem point_links_checked55565 : (cuts55565.take 1).map (fun c => (7286947841-1+2*2^10*c.k,112967136301069+c.lower,112967524167583+c.upper)) = pointBounds55565 := by
 decide +kernel
def cuts55566 : List PrefixCut := [⟨57,198307251,198307362⟩,
⟨64,223066464,223066589⟩]
theorem checked55566 : checkPrefixCuts (2^48) 7287078913 10 Manual.Count131072.C055566.packed 64 cuts55566 = true := by
 decide +kernel
def pointBounds55566 : List (Nat × Nat × Nat) := [(7287195648,112967558876216,112967946742967)]
theorem point_links_checked55566 : (cuts55566.take 1).map (fun c => (7287078913-1+2*2^10*c.k,112967360568965+c.lower,112967748435605+c.upper)) = pointBounds55566 := by
 decide +kernel
def cuts55567 : List PrefixCut := [⟨64,224761981,224762104⟩]
theorem checked55567 : checkPrefixCuts (2^48) 7287209985 10 Manual.Count131072.C055567.packed 64 cuts55567 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000173
