import PlattAssemblyKernel
import PlattCertificates.Count131072.C031120
import PlattCertificates.Count131072.C031121
import PlattCertificates.Count131072.C031122
import PlattCertificates.Count131072.C031123
import PlattCertificates.Count131072.C031124
import PlattCertificates.Count131072.C031125
import PlattCertificates.Count131072.C031126
import PlattCertificates.Count131072.C031127
import PlattCertificates.Count131072.C031128
import PlattCertificates.Count131072.C031129
import PlattCertificates.Count131072.C031130
import PlattCertificates.Count131072.C031131
import PlattCertificates.Count131072.C031132
import PlattCertificates.Count131072.C031133
import PlattCertificates.Count131072.C031134
import PlattCertificates.Count131072.C031135
import PlattCertificates.Count131072.C031136
import PlattCertificates.Count131072.C031137
import PlattCertificates.Count131072.C031138
import PlattCertificates.Count131072.C031139
import PlattCertificates.Count131072.C031140
import PlattCertificates.Count131072.C031141
import PlattCertificates.Count131072.C031142
import PlattCertificates.Count131072.C031143
import PlattCertificates.Count131072.C031144
import PlattCertificates.Count131072.C031145
import PlattCertificates.Count131072.C031146
import PlattCertificates.Count131072.C031147
import PlattCertificates.Count131072.C031148
import PlattCertificates.Count131072.C031149
import PlattCertificates.Count131072.C031150
import PlattCertificates.Count131072.C031151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31120 : List PrefixCut := [⟨20,60253470,60253503⟩,
⟨128,399708071,399708300⟩]
theorem checked31120 : checkPrefixCuts (2^48) 4082892801 9 Manual.Count131072.C031120.packed 128 cuts31120 = true := by
 decide +kernel
def pointBounds31120 : List (Nat × Nat × Nat) := [(4082913280,105694088323585,105694471907070)]
theorem point_links_checked31120 : (cuts31120.take 1).map (fun c => (4082892801-1+2*2^9*c.k,105694028070115+c.lower,105694411653567+c.upper)) = pointBounds31120 := by
 decide +kernel
def cuts31121 : List PrefixCut := [⟨17,56735734,56735766⟩,
⟨128,410380469,410380696⟩]
theorem checked31121 : checkPrefixCuts (2^48) 4083023873 9 Manual.Count131072.C031121.packed 128 cuts31121 = true := by
 decide +kernel
def pointBounds31121 : List (Nat × Nat × Nat) := [(4083041280,105694484513920,105694868097633)]
theorem point_links_checked31121 : (cuts31121.take 1).map (fun c => (4083023873-1+2*2^9*c.k,105694427778186+c.lower,105694811361867+c.upper)) = pointBounds31121 := by
 decide +kernel
def cuts31122 : List PrefixCut := [⟨14,45911053,45911079⟩,
⟨128,413055713,413055946⟩]
theorem checked31122 : checkPrefixCuts (2^48) 4083154945 9 Manual.Count131072.C031122.packed 128 cuts31122 = true := by
 decide +kernel
def pointBounds31122 : List (Nat × Nat × Nat) := [(4083169280,105694884069708,105695267653642)]
theorem point_links_checked31122 : (cuts31122.take 1).map (fun c => (4083154945-1+2*2^9*c.k,105694838158655+c.lower,105695221742563+c.upper)) = pointBounds31122 := by
 decide +kernel
def cuts31123 : List PrefixCut := [⟨11,35569599,35569621⟩,
⟨128,410009498,410009732⟩]
theorem checked31123 : checkPrefixCuts (2^48) 4083286017 9 Manual.Count131072.C031123.packed 128 cuts31123 = true := by
 decide +kernel
def pointBounds31123 : List (Nat × Nat × Nat) := [(4083297280,105695286783967,105695670368130)]
theorem point_links_checked31123 : (cuts31123.take 1).map (fun c => (4083286017-1+2*2^9*c.k,105695251214368+c.lower,105695634798509+c.upper)) = pointBounds31123 := by
 decide +kernel
def cuts31124 : List PrefixCut := [⟨8,26469561,26469575⟩,
⟨128,409307013,409307238⟩]
theorem checked31124 : checkPrefixCuts (2^48) 4083417089 9 Manual.Count131072.C031124.packed 128 cuts31124 = true := by
 decide +kernel
def pointBounds31124 : List (Nat × Nat × Nat) := [(4083425280,105695687693427,105696071277816)]
theorem point_links_checked31124 : (cuts31124.take 1).map (fun c => (4083417089-1+2*2^9*c.k,105695661223866+c.lower,105696044808241+c.upper)) = pointBounds31124 := by
 decide +kernel
def cuts31125 : List PrefixCut := [⟨5,15991518,15991527⟩,
⟨128,407432826,407433060⟩]
theorem checked31125 : checkPrefixCuts (2^48) 4083548161 9 Manual.Count131072.C031125.packed 128 cuts31125 = true := by
 decide +kernel
def pointBounds31125 : List (Nat × Nat × Nat) := [(4083553280,105696086522397,105696470107006)]
theorem point_links_checked31125 : (cuts31125.take 1).map (fun c => (4083548161-1+2*2^9*c.k,105696070530879+c.lower,105696454115479+c.upper)) = pointBounds31125 := by
 decide +kernel
def cuts31126 : List PrefixCut := [⟨2,5720922,5720926⟩,
⟨127,400251464,400251698⟩,
⟨128,403421995,403422231⟩]
theorem checked31126 : checkPrefixCuts (2^48) 4083679233 9 Manual.Count131072.C031126.packed 128 cuts31126 = true := by
 decide +kernel
def pointBounds31126 : List (Nat × Nat × Nat) := [(4083681280,105696483684627,105696867269465),(4083809280,105696878215169,105697261800237)]
theorem point_links_checked31126 : (cuts31126.take 2).map (fun c => (4083679233-1+2*2^9*c.k,105696477963705+c.lower,105696861548539+c.upper)) = pointBounds31126 := by
 decide +kernel
def cuts31127 : List PrefixCut := [⟨124,388935360,388935575⟩,
⟨128,401341392,401341615⟩]
theorem checked31127 : checkPrefixCuts (2^48) 4083810305 9 Manual.Count131072.C031127.packed 128 cuts31127 = true := by
 decide +kernel
def pointBounds31127 : List (Nat × Nat × Nat) := [(4083937280,105697270321060,105697653906345)]
theorem point_links_checked31127 : (cuts31127.take 1).map (fun c => (4083810305-1+2*2^9*c.k,105696881385700+c.lower,105697264970770+c.upper)) = pointBounds31127 := by
 decide +kernel
def cuts31128 : List PrefixCut := [⟨121,390439297,390439514⟩,
⟨128,413665410,413665639⟩]
theorem checked31128 : checkPrefixCuts (2^48) 4083941377 9 Manual.Count131072.C031128.packed 128 cuts31128 = true := by
 decide +kernel
def pointBounds31128 : List (Nat × Nat × Nat) := [(4084065280,105697673166389,105698056751899)]
theorem point_links_checked31128 : (cuts31128.take 1).map (fun c => (4083941377-1+2*2^9*c.k,105697282727092+c.lower,105697666312385+c.upper)) = pointBounds31128 := by
 decide +kernel
def cuts31129 : List PrefixCut := [⟨118,378572815,378573027⟩,
⟨128,411171040,411171271⟩]
theorem checked31129 : checkPrefixCuts (2^48) 4084072449 9 Manual.Count131072.C031129.packed 128 cuts31129 = true := by
 decide +kernel
def pointBounds31129 : List (Nat × Nat × Nat) := [(4084193280,105698074965317,105698458551051)]
theorem point_links_checked31129 : (cuts31129.take 1).map (fun c => (4084072449-1+2*2^9*c.k,105697696392502+c.lower,105698079978024+c.upper)) = pointBounds31129 := by
 decide +kernel
def cuts31130 : List PrefixCut := [⟨115,364226039,364226253⟩,
⟨128,406402536,406402774⟩]
theorem checked31130 : checkPrefixCuts (2^48) 4084203521 9 Manual.Count131072.C031130.packed 128 cuts31130 = true := by
 decide +kernel
def pointBounds31130 : List (Nat × Nat × Nat) := [(4084321280,105698471789581,105698855375548)]
theorem point_links_checked31130 : (cuts31130.take 1).map (fun c => (4084203521-1+2*2^9*c.k,105698107563542+c.lower,105698491149295+c.upper)) = pointBounds31130 := by
 decide +kernel
def cuts31131 : List PrefixCut := [⟨112,361182255,361182456⟩,
⟨128,414659255,414659484⟩]
theorem checked31131 : checkPrefixCuts (2^48) 4084334593 9 Manual.Count131072.C031131.packed 128 cuts31131 = true := by
 decide +kernel
def pointBounds31131 : List (Nat × Nat × Nat) := [(4084449280,105698875148333,105699258734525)]
theorem point_links_checked31131 : (cuts31131.take 1).map (fun c => (4084334593-1+2*2^9*c.k,105698513966078+c.lower,105698897552069+c.upper)) = pointBounds31131 := by
 decide +kernel
def cuts31132 : List PrefixCut := [⟨109,350420471,350420668⟩,
⟨128,414025754,414025987⟩]
theorem checked31132 : checkPrefixCuts (2^48) 4084465665 9 Manual.Count131072.C031132.packed 128 cuts31132 = true := by
 decide +kernel
def pointBounds31132 : List (Nat × Nat × Nat) := [(4084577280,105699279045804,105699662632221)]
theorem point_links_checked31132 : (cuts31132.take 1).map (fun c => (4084465665-1+2*2^9*c.k,105698928625333+c.lower,105699312211553+c.upper)) = pointBounds31132 := by
 decide +kernel
def cuts31133 : List PrefixCut := [⟨106,340072800,340072999⟩,
⟨128,409326633,409326871⟩]
theorem checked31133 : checkPrefixCuts (2^48) 4084596737 9 Manual.Count131072.C031133.packed 128 cuts31133 = true := by
 decide +kernel
def pointBounds31133 : List (Nat × Nat × Nat) := [(4084705280,105699682723887,105700066310539)]
theorem point_links_checked31133 : (cuts31133.take 1).map (fun c => (4084596737-1+2*2^9*c.k,105699342651087+c.lower,105699726237540+c.upper)) = pointBounds31133 := by
 decide +kernel
def cuts31134 : List PrefixCut := [⟨103,322972764,322972950⟩,
⟨128,399873094,399873322⟩]
theorem checked31134 : checkPrefixCuts (2^48) 4084727809 9 Manual.Count131072.C031134.packed 128 cuts31134 = true := by
 decide +kernel
def pointBounds31134 : List (Nat × Nat × Nat) := [(4084833280,105700074950484,105700458537361)]
theorem point_links_checked31134 : (cuts31134.take 1).map (fun c => (4084727809-1+2*2^9*c.k,105699751977720+c.lower,105700135564411+c.upper)) = pointBounds31134 := by
 decide +kernel
def cuts31135 : List PrefixCut := [⟨100,320619762,320619939⟩,
⟨128,410265060,410265284⟩]
theorem checked31135 : checkPrefixCuts (2^48) 4084858881 9 Manual.Count131072.C031135.packed 128 cuts31135 = true := by
 decide +kernel
def pointBounds31135 : List (Nat × Nat × Nat) := [(4084961280,105700472470576,105700856057672)]
theorem point_links_checked31135 : (cuts31135.take 1).map (fun c => (4084858881-1+2*2^9*c.k,105700151850814+c.lower,105700535437733+c.upper)) = pointBounds31135 := by
 decide +kernel
def cuts31136 : List PrefixCut := [⟨97,311652030,311652211⟩,
⟨128,415350639,415350875⟩]
theorem checked31136 : checkPrefixCuts (2^48) 4084989953 9 Manual.Count131072.C031136.packed 128 cuts31136 = true := by
 decide +kernel
def pointBounds31136 : List (Nat × Nat × Nat) := [(4085089280,105700873767904,105701257355228)]
theorem point_links_checked31136 : (cuts31136.take 1).map (fun c => (4084989953-1+2*2^9*c.k,105700562115874+c.lower,105700945703017+c.upper)) = pointBounds31136 := by
 decide +kernel
def cuts31137 : List PrefixCut := [⟨94,292211879,292212050⟩,
⟨128,401281436,401281667⟩]
theorem checked31137 : checkPrefixCuts (2^48) 4085121025 9 Manual.Count131072.C031137.packed 128 cuts31137 = true := by
 decide +kernel
def pointBounds31137 : List (Nat × Nat × Nat) := [(4085217280,105701269678392,105701653265942)]
theorem point_links_checked31137 : (cuts31137.take 1).map (fun c => (4085121025-1+2*2^9*c.k,105700977466513+c.lower,105701361053892+c.upper)) = pointBounds31137 := by
 decide +kernel
def cuts31138 : List PrefixCut := [⟨91,292064821,292064984⟩,
⟨128,410363303,410363533⟩]
theorem checked31138 : checkPrefixCuts (2^48) 4085252097 9 Manual.Count131072.C031138.packed 128 cuts31138 = true := by
 decide +kernel
def pointBounds31138 : List (Nat × Nat × Nat) := [(4085345280,105701670812770,105702054400543)]
theorem point_links_checked31138 : (cuts31138.take 1).map (fun c => (4085252097-1+2*2^9*c.k,105701378747949+c.lower,105701762335559+c.upper)) = pointBounds31138 := by
 decide +kernel
def cuts31139 : List PrefixCut := [⟨88,281376489,281376644⟩,
⟨128,412899295,412899523⟩]
theorem checked31139 : checkPrefixCuts (2^48) 4085383169 9 Manual.Count131072.C031139.packed 128 cuts31139 = true := by
 decide +kernel
def pointBounds31139 : List (Nat × Nat × Nat) := [(4085473280,105702070487741,105702454075736)]
theorem point_links_checked31139 : (cuts31139.take 1).map (fun c => (4085383169-1+2*2^9*c.k,105701789111252+c.lower,105702172699092+c.upper)) = pointBounds31139 := by
 decide +kernel
def cuts31140 : List PrefixCut := [⟨85,269793221,269793374⟩,
⟨128,404205400,404205631⟩]
theorem checked31140 : checkPrefixCuts (2^48) 4085514241 9 Manual.Count131072.C031140.packed 128 cuts31140 = true := by
 decide +kernel
def pointBounds31140 : List (Nat × Nat × Nat) := [(4085601280,105702471803768,105702855391989)]
theorem point_links_checked31140 : (cuts31140.take 1).map (fun c => (4085514241-1+2*2^9*c.k,105702202010547+c.lower,105702585598615+c.upper)) = pointBounds31140 := by
 decide +kernel
def cuts31141 : List PrefixCut := [⟨82,263928764,263928917⟩,
⟨128,407499281,407499516⟩]
theorem checked31141 : checkPrefixCuts (2^48) 4085645313 9 Manual.Count131072.C031141.packed 128 cuts31141 = true := by
 decide +kernel
def pointBounds31141 : List (Nat × Nat × Nat) := [(4085729280,105702870144711,105703253733163)]
theorem point_links_checked31141 : (cuts31141.take 1).map (fun c => (4085645313-1+2*2^9*c.k,105702606215947+c.lower,105702989804246+c.upper)) = pointBounds31141 := by
 decide +kernel
def cuts31142 : List PrefixCut := [⟨79,250211120,250211256⟩,
⟨128,403628306,403628529⟩]
theorem checked31142 : checkPrefixCuts (2^48) 4085776385 9 Manual.Count131072.C031142.packed 128 cuts31142 = true := by
 decide +kernel
def pointBounds31142 : List (Nat × Nat × Nat) := [(4085857280,105703263926348,105703647515018)]
theorem point_links_checked31142 : (cuts31142.take 1).map (fun c => (4085776385-1+2*2^9*c.k,105703013715228+c.lower,105703397303762+c.upper)) = pointBounds31142 := by
 decide +kernel
def cuts31143 : List PrefixCut := [⟨76,245449910,245450042⟩,
⟨128,411261994,411262219⟩]
theorem checked31143 : checkPrefixCuts (2^48) 4085907457 9 Manual.Count131072.C031143.packed 128 cuts31143 = true := by
 decide +kernel
def pointBounds31143 : List (Nat × Nat × Nat) := [(4085985280,105703662793444,105704046382333)]
theorem point_links_checked31143 : (cuts31143.take 1).map (fun c => (4085907457-1+2*2^9*c.k,105703417343534+c.lower,105703800932291+c.upper)) = pointBounds31143 := by
 decide +kernel
def cuts31144 : List PrefixCut := [⟨73,233731442,233731574⟩,
⟨128,410146566,410146797⟩]
theorem checked31144 : checkPrefixCuts (2^48) 4086038529 9 Manual.Count131072.C031144.packed 128 cuts31144 = true := by
 decide +kernel
def pointBounds31144 : List (Nat × Nat × Nat) := [(4086113280,105704062336970,105704445926084)]
theorem point_links_checked31144 : (cuts31144.take 1).map (fun c => (4086038529-1+2*2^9*c.k,105703828605528+c.lower,105704212194510+c.upper)) = pointBounds31144 := by
 decide +kernel
def cuts31145 : List PrefixCut := [⟨70,226008991,226009120⟩,
⟨128,411028897,411029133⟩]
theorem checked31145 : checkPrefixCuts (2^48) 4086169601 9 Manual.Count131072.C031145.packed 128 cuts31145 = true := by
 decide +kernel
def pointBounds31145 : List (Nat × Nat × Nat) := [(4086241280,105704464761085,105704848350427)]
theorem point_links_checked31145 : (cuts31145.take 1).map (fun c => (4086169601-1+2*2^9*c.k,105704238752094+c.lower,105704622341307+c.upper)) = pointBounds31145 := by
 decide +kernel
def cuts31146 : List PrefixCut := [⟨67,210847783,210847900⟩,
⟨128,404196449,404196670⟩]
theorem checked31146 : checkPrefixCuts (2^48) 4086300673 9 Manual.Count131072.C031146.packed 128 cuts31146 = true := by
 decide +kernel
def pointBounds31146 : List (Nat × Nat × Nat) := [(4086369280,105704860628774,105705244218340)]
theorem point_links_checked31146 : (cuts31146.take 1).map (fun c => (4086300673-1+2*2^9*c.k,105704649780991+c.lower,105705033370440+c.upper)) = pointBounds31146 := by
 decide +kernel
def cuts31147 : List PrefixCut := [⟨64,203884224,203884341⟩,
⟨128,410038163,410038395⟩]
theorem checked31147 : checkPrefixCuts (2^48) 4086431745 9 Manual.Count131072.C031147.packed 128 cuts31147 = true := by
 decide +kernel
def pointBounds31147 : List (Nat × Nat × Nat) := [(4086497280,105705257861664,105705641451451)]
theorem point_links_checked31147 : (cuts31147.take 1).map (fun c => (4086431745-1+2*2^9*c.k,105705053977440+c.lower,105705437567110+c.upper)) = pointBounds31147 := by
 decide +kernel
def cuts31148 : List PrefixCut := [⟨61,197747661,197747772⟩,
⟨128,410093972,410094206⟩]
theorem checked31148 : checkPrefixCuts (2^48) 4086562817 9 Manual.Count131072.C031148.packed 128 cuts31148 = true := by
 decide +kernel
def pointBounds31148 : List (Nat × Nat × Nat) := [(4086625280,105705661763264,105706045353277)]
theorem point_links_checked31148 : (cuts31148.take 1).map (fun c => (4086562817-1+2*2^9*c.k,105705464015603+c.lower,105705847605505+c.upper)) = pointBounds31148 := by
 decide +kernel
def cuts31149 : List PrefixCut := [⟨58,189269721,189269823⟩,
⟨128,415728552,415728778⟩]
theorem checked31149 : checkPrefixCuts (2^48) 4086693889 9 Manual.Count131072.C031149.packed 128 cuts31149 = true := by
 decide +kernel
def pointBounds31149 : List (Nat × Nat × Nat) := [(4086753280,105706063379296,105706446969534)]
theorem point_links_checked31149 : (cuts31149.take 1).map (fun c => (4086693889-1+2*2^9*c.k,105705874109575+c.lower,105706257699711+c.upper)) = pointBounds31149 := by
 decide +kernel
def cuts31150 : List PrefixCut := [⟨55,175489079,175489178⟩,
⟨128,402973827,402974054⟩]
theorem checked31150 : checkPrefixCuts (2^48) 4086824961 9 Manual.Count131072.C031150.packed 128 cuts31150 = true := by
 decide +kernel
def pointBounds31150 : List (Nat × Nat × Nat) := [(4086881280,105706465327206,105706848917667)]
theorem point_links_checked31150 : (cuts31150.take 1).map (fun c => (4086824961-1+2*2^9*c.k,105706289838127+c.lower,105706673428489+c.upper)) = pointBounds31150 := by
 decide +kernel
def cuts31151 : List PrefixCut := [⟨52,168114297,168114392⟩,
⟨128,407988401,407988634⟩]
theorem checked31151 : checkPrefixCuts (2^48) 4086956033 9 Manual.Count131072.C031151.packed 128 cuts31151 = true := by
 decide +kernel
def pointBounds31151 : List (Nat × Nat × Nat) := [(4087009280,105706860926251,105707244516935)]
theorem point_links_checked31151 : (cuts31151.take 1).map (fun c => (4086956033-1+2*2^9*c.k,105706692811954+c.lower,105707076402543+c.upper)) = pointBounds31151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000035
