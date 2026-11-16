import PlattAssemblyKernel
import PlattCertificates.Count131072.C065440
import PlattCertificates.Count131072.C065441
import PlattCertificates.Count131072.C065442
import PlattCertificates.Count131072.C065443
import PlattCertificates.Count131072.C065444
import PlattCertificates.Count131072.C065445
import PlattCertificates.Count131072.C065446
import PlattCertificates.Count131072.C065447
import PlattCertificates.Count131072.C065448
import PlattCertificates.Count131072.C065449
import PlattCertificates.Count131072.C065450
import PlattCertificates.Count131072.C065451
import PlattCertificates.Count131072.C065452
import PlattCertificates.Count131072.C065453
import PlattCertificates.Count131072.C065454
import PlattCertificates.Count131072.C065455
import PlattCertificates.Count131072.C065456
import PlattCertificates.Count131072.C065457
import PlattCertificates.Count131072.C065458
import PlattCertificates.Count131072.C065459
import PlattCertificates.Count131072.C065460
import PlattCertificates.Count131072.C065461
import PlattCertificates.Count131072.C065462
import PlattCertificates.Count131072.C065463
import PlattCertificates.Count131072.C065464
import PlattCertificates.Count131072.C065465
import PlattCertificates.Count131072.C065466
import PlattCertificates.Count131072.C065467
import PlattCertificates.Count131072.C065468
import PlattCertificates.Count131072.C065469
import PlattCertificates.Count131072.C065470
import PlattCertificates.Count131072.C065471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65440 : List PrefixCut := [⟨64,190211686,190211798⟩]
theorem checked65440 : checkPrefixCuts (2^48) 8581283841 10 Manual.Count131072.C065440.packed 64 cuts65440 = true := by
 decide +kernel
def cuts65441 : List PrefixCut := [⟨6,17646668,17646678⟩,
⟨64,187617553,187617664⟩]
theorem checked65441 : checkPrefixCuts (2^48) 8581414913 10 Manual.Count131072.C065441.packed 64 cuts65441 = true := by
 decide +kernel
def pointBounds65441 : List (Nat × Nat × Nat) := [(8581427200,114986620214473,114987009236812)]
theorem point_links_checked65441 : (cuts65441.take 1).map (fun c => (8581414913-1+2*2^10*c.k,114986602567805+c.lower,114986991590134+c.upper)) = pointBounds65441 := by
 decide +kernel
def cuts65442 : List PrefixCut := [⟨64,188467487,188467593⟩]
theorem checked65442 : checkPrefixCuts (2^48) 8581545985 10 Manual.Count131072.C065442.packed 64 cuts65442 = true := by
 decide +kernel
def cuts65443 : List PrefixCut := [⟨9,26141190,26141206⟩,
⟨64,188333410,188333518⟩]
theorem checked65443 : checkPrefixCuts (2^48) 8581677057 10 Manual.Count131072.C065443.packed 64 cuts65443 = true := by
 decide +kernel
def pointBounds65443 : List (Nat × Nat × Nat) := [(8581695488,114987004794035,114987393816597)]
theorem point_links_checked65443 : (cuts65443.take 1).map (fun c => (8581677057-1+2*2^10*c.k,114986978652845+c.lower,114987367675391+c.upper)) = pointBounds65443 := by
 decide +kernel
def cuts65444 : List PrefixCut := [⟨64,186756187,186756293⟩]
theorem checked65444 : checkPrefixCuts (2^48) 8581808129 10 Manual.Count131072.C065444.packed 64 cuts65444 = true := by
 decide +kernel
def cuts65445 : List PrefixCut := [⟨12,35553543,35553565⟩,
⟨64,187376517,187376625⟩]
theorem checked65445 : checkPrefixCuts (2^48) 8581939201 10 Manual.Count131072.C065445.packed 64 cuts65445 = true := by
 decide +kernel
def pointBounds65445 : List (Nat × Nat × Nat) := [(8581963776,114987389295985,114987778318767)]
theorem point_links_checked65445 : (cuts65445.take 1).map (fun c => (8581939201-1+2*2^10*c.k,114987353742442+c.lower,114987742765202+c.upper)) = pointBounds65445 := by
 decide +kernel
def cuts65446 : List PrefixCut := [⟨64,187406420,187406528⟩]
theorem checked65446 : checkPrefixCuts (2^48) 8582070273 10 Manual.Count131072.C065446.packed 64 cuts65446 = true := by
 decide +kernel
def cuts65447 : List PrefixCut := [⟨15,43423832,43423858⟩,
⟨64,187731551,187731660⟩]
theorem checked65447 : checkPrefixCuts (2^48) 8582201345 10 Manual.Count131072.C065447.packed 64 cuts65447 = true := by
 decide +kernel
def pointBounds65447 : List (Nat × Nat × Nat) := [(8582232064,114987771949211,114988160972213)]
theorem point_links_checked65447 : (cuts65447.take 1).map (fun c => (8582201345-1+2*2^10*c.k,114987728525379+c.lower,114988117548355+c.upper)) = pointBounds65447 := by
 decide +kernel
def cuts65448 : List PrefixCut := [⟨64,186613598,186613713⟩]
theorem checked65448 : checkPrefixCuts (2^48) 8582332417 10 Manual.Count131072.C065448.packed 64 cuts65448 = true := by
 decide +kernel
def cuts65449 : List PrefixCut := [⟨18,53031852,53031882⟩,
⟨64,185331702,185331803⟩]
theorem checked65449 : checkPrefixCuts (2^48) 8582463489 10 Manual.Count131072.C065449.packed 64 cuts65449 = true := by
 decide +kernel
def pointBounds65449 : List (Nat × Nat × Nat) := [(8582500352,114988155902380,114988544925610)]
theorem point_links_checked65449 : (cuts65449.take 1).map (fun c => (8582463489-1+2*2^10*c.k,114988102870528+c.lower,114988491893728+c.upper)) = pointBounds65449 := by
 decide +kernel
def cuts65450 : List PrefixCut := [⟨64,187067040,187067151⟩]
theorem checked65450 : checkPrefixCuts (2^48) 8582594561 10 Manual.Count131072.C065450.packed 64 cuts65450 = true := by
 decide +kernel
def cuts65451 : List PrefixCut := [⟨21,62147345,62147380⟩,
⟨64,189917360,189917473⟩]
theorem checked65451 : checkPrefixCuts (2^48) 8582725633 10 Manual.Count131072.C065451.packed 64 cuts65451 = true := by
 decide +kernel
def pointBounds65451 : List (Nat × Nat × Nat) := [(8582768640,114988537416615,114988926440062)]
theorem point_links_checked65451 : (cuts65451.take 1).map (fun c => (8582725633-1+2*2^10*c.k,114988475269270+c.lower,114988864292682+c.upper)) = pointBounds65451 := by
 decide +kernel
def cuts65452 : List PrefixCut := [⟨64,187225283,187225391⟩]
theorem checked65452 : checkPrefixCuts (2^48) 8582856705 10 Manual.Count131072.C065452.packed 64 cuts65452 = true := by
 decide +kernel
def cuts65453 : List PrefixCut := [⟨24,70245643,70245685⟩,
⟨64,188206261,188206372⟩]
theorem checked65453 : checkPrefixCuts (2^48) 8582987777 10 Manual.Count131072.C065453.packed 64 cuts65453 = true := by
 decide +kernel
def pointBounds65453 : List (Nat × Nat × Nat) := [(8583036928,114988922657556,114989311681231)]
theorem point_links_checked65453 : (cuts65453.take 1).map (fun c => (8582987777-1+2*2^10*c.k,114988852411913+c.lower,114989241435546+c.upper)) = pointBounds65453 := by
 decide +kernel
def cuts65454 : List PrefixCut := [⟨64,187777067,187777176⟩]
theorem checked65454 : checkPrefixCuts (2^48) 8583118849 10 Manual.Count131072.C065454.packed 64 cuts65454 = true := by
 decide +kernel
def cuts65455 : List PrefixCut := [⟨27,78605789,78605837⟩,
⟨64,187183921,187184034⟩]
theorem checked65455 : checkPrefixCuts (2^48) 8583249921 10 Manual.Count131072.C065455.packed 64 cuts65455 = true := by
 decide +kernel
def pointBounds65455 : List (Nat × Nat × Nat) := [(8583305216,114989307001030,114989696024931)]
theorem point_links_checked65455 : (cuts65455.take 1).map (fun c => (8583249921-1+2*2^10*c.k,114989228395241+c.lower,114989617419094+c.upper)) = pointBounds65455 := by
 decide +kernel
def cuts65456 : List PrefixCut := [⟨64,186066118,186066222⟩]
theorem checked65456 : checkPrefixCuts (2^48) 8583380993 10 Manual.Count131072.C065456.packed 64 cuts65456 = true := by
 decide +kernel
def cuts65457 : List PrefixCut := [⟨30,87391725,87391775⟩,
⟨64,187735679,187735784⟩]
theorem checked65457 : checkPrefixCuts (2^48) 8583512065 10 Manual.Count131072.C065457.packed 64 cuts65457 = true := by
 decide +kernel
def pointBounds65457 : List (Nat × Nat × Nat) := [(8583573504,114989689037005,114990078061125)]
theorem point_links_checked65457 : (cuts65457.take 1).map (fun c => (8583512065-1+2*2^10*c.k,114989601645280+c.lower,114989990669350+c.upper)) = pointBounds65457 := by
 decide +kernel
def cuts65458 : List PrefixCut := [⟨64,189929869,189929979⟩]
theorem checked65458 : checkPrefixCuts (2^48) 8583643137 10 Manual.Count131072.C065458.packed 64 cuts65458 = true := by
 decide +kernel
def cuts65459 : List PrefixCut := [⟨33,99259508,99259566⟩,
⟨64,189631852,189631965⟩]
theorem checked65459 : checkPrefixCuts (2^48) 8583774209 10 Manual.Count131072.C065459.packed 64 cuts65459 = true := by
 decide +kernel
def pointBounds65459 : List (Nat × Nat × Nat) := [(8583841792,114990078570336,114990467594679)]
theorem point_links_checked65459 : (cuts65459.take 1).map (fun c => (8583774209-1+2*2^10*c.k,114989979310828+c.lower,114990368335113+c.upper)) = pointBounds65459 := by
 decide +kernel
def cuts65460 : List PrefixCut := [⟨64,186710568,186710671⟩]
theorem checked65460 : checkPrefixCuts (2^48) 8583905281 10 Manual.Count131072.C065460.packed 64 cuts65460 = true := by
 decide +kernel
def cuts65461 : List PrefixCut := [⟨36,105880084,105880146⟩,
⟨64,189330926,189331036⟩]
theorem checked65461 : checkPrefixCuts (2^48) 8584036353 10 Manual.Count131072.C065461.packed 64 cuts65461 = true := by
 decide +kernel
def pointBounds65461 : List (Nat × Nat × Nat) := [(8584110080,114990461533332,114990850557895)]
theorem point_links_checked65461 : (cuts65461.take 1).map (fun c => (8584036353-1+2*2^10*c.k,114990355653248+c.lower,114990744677749+c.upper)) = pointBounds65461 := by
 decide +kernel
def cuts65462 : List PrefixCut := [⟨64,185294904,185295012⟩]
theorem checked65462 : checkPrefixCuts (2^48) 8584167425 10 Manual.Count131072.C065462.packed 64 cuts65462 = true := by
 decide +kernel
def cuts65463 : List PrefixCut := [⟨39,114861098,114861167⟩,
⟨64,190767871,190767982⟩]
theorem checked65463 : checkPrefixCuts (2^48) 8584298497 10 Manual.Count131072.C065463.packed 64 cuts65463 = true := by
 decide +kernel
def pointBounds65463 : List (Nat × Nat × Nat) := [(8584378368,114990845140176,114991234164964)]
theorem point_links_checked65463 : (cuts65463.take 1).map (fun c => (8584298497-1+2*2^10*c.k,114990730279078+c.lower,114991119303797+c.upper)) = pointBounds65463 := by
 decide +kernel
def cuts65464 : List PrefixCut := [⟨64,187027057,187027170⟩]
theorem checked65464 : checkPrefixCuts (2^48) 8584429569 10 Manual.Count131072.C065464.packed 64 cuts65464 = true := by
 decide +kernel
def cuts65465 : List PrefixCut := [⟨42,125284245,125284314⟩,
⟨64,189221019,189221126⟩]
theorem checked65465 : checkPrefixCuts (2^48) 8584560641 10 Manual.Count131072.C065465.packed 64 cuts65465 = true := by
 decide +kernel
def pointBounds65465 : List (Nat × Nat × Nat) := [(8584646656,114991233358251,114991622383263)]
theorem point_links_checked65465 : (cuts65465.take 1).map (fun c => (8584560641-1+2*2^10*c.k,114991108074006+c.lower,114991497098949+c.upper)) = pointBounds65465 := by
 decide +kernel
def cuts65466 : List PrefixCut := [⟨64,185906558,185906666⟩]
theorem checked65466 : checkPrefixCuts (2^48) 8584691713 10 Manual.Count131072.C065466.packed 64 cuts65466 = true := by
 decide +kernel
def cuts65467 : List PrefixCut := [⟨45,132493583,132493662⟩,
⟨64,189313585,189313695⟩]
theorem checked65467 : checkPrefixCuts (2^48) 8584822785 10 Manual.Count131072.C065467.packed 64 cuts65467 = true := by
 decide +kernel
def pointBounds65467 : List (Nat × Nat × Nat) := [(8584914944,114991615695166,114992004720403)]
theorem point_links_checked65467 : (cuts65467.take 1).map (fun c => (8584822785-1+2*2^10*c.k,114991483201583+c.lower,114991872226741+c.upper)) = pointBounds65467 := by
 decide +kernel
def cuts65468 : List PrefixCut := [⟨64,189900857,189900966⟩]
theorem checked65468 : checkPrefixCuts (2^48) 8584953857 10 Manual.Count131072.C065468.packed 64 cuts65468 = true := by
 decide +kernel
def cuts65469 : List PrefixCut := [⟨48,142128679,142128758⟩,
⟨64,189012747,189012856⟩]
theorem checked65469 : checkPrefixCuts (2^48) 8585084929 10 Manual.Count131072.C065469.packed 64 cuts65469 = true := by
 decide +kernel
def pointBounds65469 : List (Nat × Nat × Nat) := [(8585183232,114992004544704,114992393570160)]
theorem point_links_checked65469 : (cuts65469.take 1).map (fun c => (8585084929-1+2*2^10*c.k,114991862416025+c.lower,114992251441402+c.upper)) = pointBounds65469 := by
 decide +kernel
def cuts65470 : List PrefixCut := [⟨64,185108338,185108446⟩]
theorem checked65470 : checkPrefixCuts (2^48) 8585216001 10 Manual.Count131072.C065470.packed 64 cuts65470 = true := by
 decide +kernel
def cuts65471 : List PrefixCut := [⟨51,149074762,149074845⟩,
⟨64,186613644,186613752⟩]
theorem checked65471 : checkPrefixCuts (2^48) 8585347073 10 Manual.Count131072.C065471.packed 64 cuts65471 = true := by
 decide +kernel
def pointBounds65471 : List (Nat × Nat × Nat) := [(8585451520,114992385611872,114992774637549)]
theorem point_links_checked65471 : (cuts65471.take 1).map (fun c => (8585347073-1+2*2^10*c.k,114992236537110+c.lower,114992625562704+c.upper)) = pointBounds65471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000170
