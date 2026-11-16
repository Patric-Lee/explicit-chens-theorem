import PlattAssemblyKernel
import PlattCertificates.Count131072.C054320
import PlattCertificates.Count131072.C054321
import PlattCertificates.Count131072.C054322
import PlattCertificates.Count131072.C054323
import PlattCertificates.Count131072.C054324
import PlattCertificates.Count131072.C054325
import PlattCertificates.Count131072.C054326
import PlattCertificates.Count131072.C054327
import PlattCertificates.Count131072.C054328
import PlattCertificates.Count131072.C054329
import PlattCertificates.Count131072.C054330
import PlattCertificates.Count131072.C054331
import PlattCertificates.Count131072.C054332
import PlattCertificates.Count131072.C054333
import PlattCertificates.Count131072.C054334
import PlattCertificates.Count131072.C054335
import PlattCertificates.Count131072.C054336
import PlattCertificates.Count131072.C054337
import PlattCertificates.Count131072.C054338
import PlattCertificates.Count131072.C054339
import PlattCertificates.Count131072.C054340
import PlattCertificates.Count131072.C054341
import PlattCertificates.Count131072.C054342
import PlattCertificates.Count131072.C054343
import PlattCertificates.Count131072.C054344
import PlattCertificates.Count131072.C054345
import PlattCertificates.Count131072.C054346
import PlattCertificates.Count131072.C054347
import PlattCertificates.Count131072.C054348
import PlattCertificates.Count131072.C054349
import PlattCertificates.Count131072.C054350
import PlattCertificates.Count131072.C054351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54320 : List PrefixCut := [⟨64,230116405,230116536⟩]
theorem checked54320 : checkPrefixCuts (2^48) 7123763201 10 Manual.Count131072.C054320.packed 64 cuts54320 = true := by
 decide +kernel
def cuts54321 : List PrefixCut := [⟨7,25168723,25168738⟩,
⟨64,231771636,231771767⟩]
theorem checked54321 : checkPrefixCuts (2^48) 7123894273 10 Manual.Count131072.C054321.packed 64 cuts54321 = true := by
 decide +kernel
def pointBounds54321 : List (Nat × Nat × Nat) := [(7123908608,112686576080893,112686963788110)]
theorem point_links_checked54321 : (cuts54321.take 1).map (fun c => (7123894273-1+2*2^10*c.k,112686550912170+c.lower,112686938619372+c.upper)) = pointBounds54321 := by
 decide +kernel
def cuts54322 : List PrefixCut := [⟨52,183762673,183762779⟩,
⟨64,226077878,226078008⟩]
theorem checked54322 : checkPrefixCuts (2^48) 7124025345 10 Manual.Count131072.C054322.packed 64 cuts54322 = true := by
 decide +kernel
def pointBounds54322 : List (Nat × Nat × Nat) := [(7124131840,112686966446479,112687354153918)]
theorem point_links_checked54322 : (cuts54322.take 1).map (fun c => (7124025345-1+2*2^10*c.k,112686782683806+c.lower,112687170391139+c.upper)) = pointBounds54322 := by
 decide +kernel
def cuts54323 : List PrefixCut := [⟨64,227614597,227614726⟩]
theorem checked54323 : checkPrefixCuts (2^48) 7124156417 10 Manual.Count131072.C054323.packed 64 cuts54323 = true := by
 decide +kernel
def cuts54324 : List PrefixCut := [⟨33,116907165,116907230⟩,
⟨64,227452362,227452489⟩]
theorem checked54324 : checkPrefixCuts (2^48) 7124287489 10 Manual.Count131072.C054324.packed 64 cuts54324 = true := by
 decide +kernel
def pointBounds54324 : List (Nat × Nat × Nat) := [(7124355072,112687353283446,112687740991103)]
theorem point_links_checked54324 : (cuts54324.take 1).map (fun c => (7124287489-1+2*2^10*c.k,112687236376281+c.lower,112687624083873+c.upper)) = pointBounds54324 := by
 decide +kernel
def cuts54325 : List PrefixCut := [⟨64,230569343,230569472⟩]
theorem checked54325 : checkPrefixCuts (2^48) 7124418561 10 Manual.Count131072.C054325.packed 64 cuts54325 = true := by
 decide +kernel
def cuts54326 : List PrefixCut := [⟨14,50253752,50253781⟩,
⟨64,227562515,227562648⟩]
theorem checked54326 : checkPrefixCuts (2^48) 7124549633 10 Manual.Count131072.C054326.packed 64 cuts54326 = true := by
 decide +kernel
def pointBounds54326 : List (Nat × Nat × Nat) := [(7124578304,112687744651738,112688132359615)]
theorem point_links_checked54326 : (cuts54326.take 1).map (fun c => (7124549633-1+2*2^10*c.k,112687694397986+c.lower,112688082105834+c.upper)) = pointBounds54326 := by
 decide +kernel
def cuts54327 : List PrefixCut := [⟨59,209701478,209701598⟩,
⟨64,227795373,227795503⟩]
theorem checked54327 : checkPrefixCuts (2^48) 7124680705 10 Manual.Count131072.C054327.packed 64 cuts54327 = true := by
 decide +kernel
def pointBounds54327 : List (Nat × Nat × Nat) := [(7124801536,112688131661979,112688519370080)]
theorem point_links_checked54327 : (cuts54327.take 1).map (fun c => (7124680705-1+2*2^10*c.k,112687921960501+c.lower,112688309668482+c.upper)) = pointBounds54327 := by
 decide +kernel
def cuts54328 : List PrefixCut := [⟨64,227791200,227791328⟩]
theorem checked54328 : checkPrefixCuts (2^48) 7124811777 10 Manual.Count131072.C054328.packed 64 cuts54328 = true := by
 decide +kernel
def cuts54329 : List PrefixCut := [⟨40,143917950,143918030⟩,
⟨64,228853644,228853773⟩]
theorem checked54329 : checkPrefixCuts (2^48) 7124942849 10 Manual.Count131072.C054329.packed 64 cuts54329 = true := by
 decide +kernel
def pointBounds54329 : List (Nat × Nat × Nat) := [(7125024768,112688521465024,112688909173343)]
theorem point_links_checked54329 : (cuts54329.take 1).map (fun c => (7124942849-1+2*2^10*c.k,112688377547074+c.lower,112688765255313+c.upper)) = pointBounds54329 := by
 decide +kernel
def cuts54330 : List PrefixCut := [⟨64,225768081,225768209⟩]
theorem checked54330 : checkPrefixCuts (2^48) 7125073921 10 Manual.Count131072.C054330.packed 64 cuts54330 = true := by
 decide +kernel
def cuts54331 : List PrefixCut := [⟨21,75808163,75808206⟩,
⟨64,229832816,229832945⟩]
theorem checked54331 : checkPrefixCuts (2^48) 7125204993 10 Manual.Count131072.C054331.packed 64 cuts54331 = true := by
 decide +kernel
def pointBounds54331 : List (Nat × Nat × Nat) := [(7125248000,112688907976962,112689295685501)]
theorem point_links_checked54331 : (cuts54331.take 1).map (fun c => (7125204993-1+2*2^10*c.k,112688832168799+c.lower,112689219877295+c.upper)) = pointBounds54331 := by
 decide +kernel
def cuts54332 : List PrefixCut := [⟨64,228998996,228999128⟩]
theorem checked54332 : checkPrefixCuts (2^48) 7125336065 10 Manual.Count131072.C054332.packed 64 cuts54332 = true := by
 decide +kernel
def cuts54333 : List PrefixCut := [⟨2,7386995,7386999⟩,
⟨64,227849268,227849394⟩]
theorem checked54333 : checkPrefixCuts (2^48) 7125467137 10 Manual.Count131072.C054333.packed 64 cuts54333 = true := by
 decide +kernel
def pointBounds54333 : List (Nat × Nat × Nat) := [(7125471232,112689298387606,112689686096367)]
theorem point_links_checked54333 : (cuts54333.take 1).map (fun c => (7125467137-1+2*2^10*c.k,112689291000611+c.lower,112689678709368+c.upper)) = pointBounds54333 := by
 decide +kernel
def cuts54334 : List PrefixCut := [⟨47,166578524,166578619⟩,
⟨64,227884544,227884673⟩]
theorem checked54334 : checkPrefixCuts (2^48) 7125598209 10 Manual.Count131072.C054334.packed 64 cuts54334 = true := by
 decide +kernel
def pointBounds54334 : List (Nat × Nat × Nat) := [(7125694464,112689685428403,112690073137381)]
theorem point_links_checked54334 : (cuts54334.take 1).map (fun c => (7125598209-1+2*2^10*c.k,112689518849879+c.lower,112689906558762+c.upper)) = pointBounds54334 := by
 decide +kernel
def cuts54335 : List PrefixCut := [⟨64,225984302,225984428⟩]
theorem checked54335 : checkPrefixCuts (2^48) 7125729281 10 Manual.Count131072.C054335.packed 64 cuts54335 = true := by
 decide +kernel
def cuts54336 : List PrefixCut := [⟨28,100251820,100251877⟩,
⟨64,230404182,230404314⟩]
theorem checked54336 : checkPrefixCuts (2^48) 7125860353 10 Manual.Count131072.C054336.packed 64 cuts54336 = true := by
 decide +kernel
def pointBounds54336 : List (Nat × Nat × Nat) := [(7125917696,112690072970545,112690460679740)]
theorem point_links_checked54336 : (cuts54336.take 1).map (fun c => (7125860353-1+2*2^10*c.k,112689972718725+c.lower,112690360427863+c.upper)) = pointBounds54336 := by
 decide +kernel
def cuts54337 : List PrefixCut := [⟨64,226686998,226687131⟩]
theorem checked54337 : checkPrefixCuts (2^48) 7125991425 10 Manual.Count131072.C054337.packed 64 cuts54337 = true := by
 decide +kernel
def cuts54338 : List PrefixCut := [⟨9,33139640,33139659⟩,
⟨64,228341781,228341913⟩]
theorem checked54338 : checkPrefixCuts (2^48) 7126122497 10 Manual.Count131072.C054338.packed 64 cuts54338 = true := by
 decide +kernel
def pointBounds54338 : List (Nat × Nat × Nat) := [(7126140928,112690462949545,112690850658967)]
theorem point_links_checked54338 : (cuts54338.take 1).map (fun c => (7126122497-1+2*2^10*c.k,112690429809905+c.lower,112690817519308+c.upper)) = pointBounds54338 := by
 decide +kernel
def cuts54339 : List PrefixCut := [⟨54,194883104,194883215⟩,
⟨64,232761331,232761462⟩]
theorem checked54339 : checkPrefixCuts (2^48) 7126253569 10 Manual.Count131072.C054339.packed 64 cuts54339 = true := by
 decide +kernel
def pointBounds54339 : List (Nat × Nat × Nat) := [(7126364160,112690853034790,112691240744436)]
theorem point_links_checked54339 : (cuts54339.take 1).map (fun c => (7126253569-1+2*2^10*c.k,112690658151686+c.lower,112691045861221+c.upper)) = pointBounds54339 := by
 decide +kernel
def cuts54340 : List PrefixCut := [⟨64,224344133,224344259⟩]
theorem checked54340 : checkPrefixCuts (2^48) 7126384641 10 Manual.Count131072.C054340.packed 64 cuts54340 = true := by
 decide +kernel
def cuts54341 : List PrefixCut := [⟨35,127258207,127258278⟩,
⟨64,231844368,231844496⟩]
theorem checked54341 : checkPrefixCuts (2^48) 7126515713 10 Manual.Count131072.C054341.packed 64 cuts54341 = true := by
 decide +kernel
def pointBounds54341 : List (Nat × Nat × Nat) := [(7126587392,112691242515357,112691630225220)]
theorem point_links_checked54341 : (cuts54341.take 1).map (fun c => (7126515713-1+2*2^10*c.k,112691115257150+c.lower,112691502966942+c.upper)) = pointBounds54341 := by
 decide +kernel
def cuts54342 : List PrefixCut := [⟨64,226192218,226192346⟩]
theorem checked54342 : checkPrefixCuts (2^48) 7126646785 10 Manual.Count131072.C054342.packed 64 cuts54342 = true := by
 decide +kernel
def cuts54343 : List PrefixCut := [⟨16,56754749,56754781⟩,
⟨64,228281269,228281399⟩]
theorem checked54343 : checkPrefixCuts (2^48) 7126777857 10 Manual.Count131072.C054343.packed 64 cuts54343 = true := by
 decide +kernel
def pointBounds54343 : List (Nat × Nat × Nat) := [(7126810624,112691630048485,112692017758565)]
theorem point_links_checked54343 : (cuts54343.take 1).map (fun c => (7126777857-1+2*2^10*c.k,112691573293736+c.lower,112691961003784+c.upper)) = pointBounds54343 := by
 decide +kernel
def cuts54344 : List PrefixCut := [⟨61,216665842,216665966⟩,
⟨64,226381356,226381485⟩]
theorem checked54344 : checkPrefixCuts (2^48) 7126908929 10 Manual.Count131072.C054344.packed 64 cuts54344 = true := by
 decide +kernel
def pointBounds54344 : List (Nat × Nat × Nat) := [(7127033856,112692018240847,112692405951149)]
theorem point_links_checked54344 : (cuts54344.take 1).map (fun c => (7126908929-1+2*2^10*c.k,112691801575005+c.lower,112692189285183+c.upper)) = pointBounds54344 := by
 decide +kernel
def cuts54345 : List PrefixCut := [⟨64,228312385,228312517⟩]
theorem checked54345 : checkPrefixCuts (2^48) 7127040001 10 Manual.Count131072.C054345.packed 64 cuts54345 = true := by
 decide +kernel
def cuts54346 : List PrefixCut := [⟨42,147585247,147585331⟩,
⟨64,226767935,226768062⟩]
theorem checked54346 : checkPrefixCuts (2^48) 7127171073 10 Manual.Count131072.C054346.packed 64 cuts54346 = true := by
 decide +kernel
def pointBounds54346 : List (Nat × Nat × Nat) := [(7127257088,112692403853993,112692791564516)]
theorem point_links_checked54346 : (cuts54346.take 1).map (fun c => (7127171073-1+2*2^10*c.k,112692256268746+c.lower,112692643979185+c.upper)) = pointBounds54346 := by
 decide +kernel
def cuts54347 : List PrefixCut := [⟨64,229725707,229725840⟩]
theorem checked54347 : checkPrefixCuts (2^48) 7127302145 10 Manual.Count131072.C054347.packed 64 cuts54347 = true := by
 decide +kernel
def cuts54348 : List PrefixCut := [⟨23,81550220,81550264⟩,
⟨64,226443681,226443807⟩]
theorem checked54348 : checkPrefixCuts (2^48) 7127433217 10 Manual.Count131072.C054348.packed 64 cuts54348 = true := by
 decide +kernel
def pointBounds54348 : List (Nat × Nat × Nat) := [(7127480320,112692794312608,112693182023351)]
theorem point_links_checked54348 : (cuts54348.take 1).map (fun c => (7127433217-1+2*2^10*c.k,112692712762388+c.lower,112693100473087+c.upper)) = pointBounds54348 := by
 decide +kernel
def cuts54349 : List PrefixCut := [⟨64,228098132,228098262⟩]
theorem checked54349 : checkPrefixCuts (2^48) 7127564289 10 Manual.Count131072.C054349.packed 64 cuts54349 = true := by
 decide +kernel
def cuts54350 : List PrefixCut := [⟨4,13979562,13979570⟩,
⟨64,228172913,228173045⟩]
theorem checked54350 : checkPrefixCuts (2^48) 7127695361 10 Manual.Count131072.C054350.packed 64 cuts54350 = true := by
 decide +kernel
def pointBounds54350 : List (Nat × Nat × Nat) := [(7127703552,112693181283763,112693568994726)]
theorem point_links_checked54350 : (cuts54350.take 1).map (fun c => (7127695361-1+2*2^10*c.k,112693167304201+c.lower,112693555015156+c.upper)) = pointBounds54350 := by
 decide +kernel
def cuts54351 : List PrefixCut := [⟨49,176991072,176991173⟩,
⟨64,233381284,233381415⟩]
theorem checked54351 : checkPrefixCuts (2^48) 7127826433 10 Manual.Count131072.C054351.packed 64 cuts54351 = true := by
 decide +kernel
def pointBounds54351 : List (Nat × Nat × Nat) := [(7127926784,112693572468186,112693960179374)]
theorem point_links_checked54351 : (cuts54351.take 1).map (fun c => (7127826433-1+2*2^10*c.k,112693395477114+c.lower,112693783188201+c.upper)) = pointBounds54351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000135
