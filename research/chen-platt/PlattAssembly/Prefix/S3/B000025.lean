import PlattAssemblyKernel
import PlattCertificates.Count131072.C020800
import PlattCertificates.Count131072.C020801
import PlattCertificates.Count131072.C020802
import PlattCertificates.Count131072.C020803
import PlattCertificates.Count131072.C020804
import PlattCertificates.Count131072.C020805
import PlattCertificates.Count131072.C020806
import PlattCertificates.Count131072.C020807
import PlattCertificates.Count131072.C020808
import PlattCertificates.Count131072.C020809
import PlattCertificates.Count131072.C020810
import PlattCertificates.Count131072.C020811
import PlattCertificates.Count131072.C020812
import PlattCertificates.Count131072.C020813
import PlattCertificates.Count131072.C020814
import PlattCertificates.Count131072.C020815
import PlattCertificates.Count131072.C020816
import PlattCertificates.Count131072.C020817
import PlattCertificates.Count131072.C020818
import PlattCertificates.Count131072.C020819
import PlattCertificates.Count131072.C020820
import PlattCertificates.Count131072.C020821
import PlattCertificates.Count131072.C020822
import PlattCertificates.Count131072.C020823
import PlattCertificates.Count131072.C020824
import PlattCertificates.Count131072.C020825
import PlattCertificates.Count131072.C020826
import PlattCertificates.Count131072.C020827
import PlattCertificates.Count131072.C020828
import PlattCertificates.Count131072.C020829
import PlattCertificates.Count131072.C020830
import PlattCertificates.Count131072.C020831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20800 : List PrefixCut := [⟨65,313407034,313407218⟩,
⟨128,615363370,615363732⟩]
theorem checked20800 : checkPrefixCuts (2^48) 2730229761 9 Manual.Count131072.C020800.packed 128 cuts20800 = true := by
 decide +kernel
def pointBounds20800 : List (Nat × Nat × Nat) := [(2730296320,100528903877709,100529284544304)]
theorem point_links_checked20800 : (cuts20800.take 1).map (fun c => (2730229761-1+2*2^9*c.k,100528590470675+c.lower,100528971137086+c.upper)) = pointBounds20800 := by
 decide +kernel
def cuts20801 : List PrefixCut := [⟨21,100409979,100410036⟩,
⟨105,500908078,500908364⟩,
⟨128,615333799,615334150⟩]
theorem checked20801 : checkPrefixCuts (2^48) 2730360833 9 Manual.Count131072.C020801.packed 128 cuts20801 = true := by
 decide +kernel
def pointBounds20801 : List (Nat × Nat × Nat) := [(2730382336,100529306244024,100529686910854),(2730468352,100529706742123,100530087409182)]
theorem point_links_checked20801 : (cuts20801.take 2).map (fun c => (2730360833-1+2*2^9*c.k,100529205834045+c.lower,100529586500818+c.upper)) = pointBounds20801 := by
 decide +kernel
def cuts20802 : List PrefixCut := [⟨61,300285465,300285641⟩,
⟨128,619427728,619428091⟩]
theorem checked20802 : checkPrefixCuts (2^48) 2730491905 9 Manual.Count131072.C020802.packed 128 cuts20802 = true := by
 decide +kernel
def pointBounds20802 : List (Nat × Nat × Nat) := [(2730554368,100530121453309,100530502120609)]
theorem point_links_checked20802 : (cuts20802.take 1).map (fun c => (2730491905-1+2*2^9*c.k,100529821167844+c.lower,100530201834968+c.upper)) = pointBounds20802 := by
 decide +kernel
def cuts20803 : List PrefixCut := [⟨17,82567486,82567535⟩,
⟨101,489109277,489109562⟩,
⟨128,618367087,618367448⟩]
theorem checked20803 : checkPrefixCuts (2^48) 2730622977 9 Manual.Count131072.C020803.packed 128 cuts20803 = true := by
 decide +kernel
def pointBounds20803 : List (Nat × Nat × Nat) := [(2730640384,100530523163058,100530903830594),(2730726400,100530929704849,100531310372621)]
theorem point_links_checked20803 : (cuts20803.take 2).map (fun c => (2730622977-1+2*2^9*c.k,100530440595572+c.lower,100530821263059+c.upper)) = pointBounds20803 := by
 decide +kernel
def cuts20804 : List PrefixCut := [⟨57,281188060,281188225⟩,
⟨128,627407924,627408293⟩]
theorem checked20804 : checkPrefixCuts (2^48) 2730754049 9 Manual.Count131072.C020804.packed 128 cuts20804 = true := by
 decide +kernel
def pointBounds20804 : List (Nat × Nat × Nat) := [(2730812416,100531340150719,100531720818732)]
theorem point_links_checked20804 : (cuts20804.take 1).map (fun c => (2730754049-1+2*2^9*c.k,100531058962659+c.lower,100531439630507+c.upper)) = pointBounds20804 := by
 decide +kernel
def cuts20805 : List PrefixCut := [⟨13,62873123,62873162⟩,
⟨97,473086968,473087248⟩,
⟨128,622121250,622121613⟩]
theorem checked20805 : checkPrefixCuts (2^48) 2730885121 9 Manual.Count131072.C020805.packed 128 cuts20805 = true := by
 decide +kernel
def pointBounds20805 : List (Nat × Nat × Nat) := [(2730898432,100531749243706,100532129911962),(2730984448,100532159457551,100532540126048)]
theorem point_links_checked20805 : (cuts20805.take 2).map (fun c => (2730885121-1+2*2^9*c.k,100531686370583+c.lower,100532067038800+c.upper)) = pointBounds20805 := by
 decide +kernel
def cuts20806 : List PrefixCut := [⟨53,254673544,254673690⟩,
⟨128,623843430,623843786⟩]
theorem checked20806 : checkPrefixCuts (2^48) 2731016193 9 Manual.Count131072.C020806.packed 128 cuts20806 = true := by
 decide +kernel
def pointBounds20806 : List (Nat × Nat × Nat) := [(2731070464,100532563165377,100532943834103)]
theorem point_links_checked20806 : (cuts20806.take 1).map (fun c => (2731016193-1+2*2^9*c.k,100532308491833+c.lower,100532689160413+c.upper)) = pointBounds20806 := by
 decide +kernel
def cuts20807 : List PrefixCut := [⟨9,44728420,44728445⟩,
⟨93,452017846,452018106⟩,
⟨128,626080741,626081099⟩]
theorem checked20807 : checkPrefixCuts (2^48) 2731147265 9 Manual.Count131072.C020807.packed 128 cuts20807 = true := by
 decide +kernel
def pointBounds20807 : List (Nat × Nat × Nat) := [(2731156480,100532977063683,100533357732644),(2731242496,100533384353109,100533765022305)]
theorem point_links_checked20807 : (cuts20807.take 2).map (fun c => (2731147265-1+2*2^9*c.k,100532932335263+c.lower,100533313004199+c.upper)) = pointBounds20807 := by
 decide +kernel
def cuts20808 : List PrefixCut := [⟨49,241252148,241252289⟩,
⟨128,630894339,630894700⟩]
theorem checked20808 : checkPrefixCuts (2^48) 2731278337 9 Manual.Count131072.C020808.packed 128 cuts20808 = true := by
 decide +kernel
def pointBounds20808 : List (Nat × Nat × Nat) := [(2731328512,100533799668152,100534180337587)]
theorem point_links_checked20808 : (cuts20808.take 1).map (fun c => (2731278337-1+2*2^9*c.k,100533558416004+c.lower,100533939085298+c.upper)) = pointBounds20808 := by
 decide +kernel
def cuts20809 : List PrefixCut := [⟨5,25762765,25762780⟩,
⟨89,440021117,440021371⟩,
⟨128,626742204,626742573⟩]
theorem checked20809 : checkPrefixCuts (2^48) 2731409409 9 Manual.Count131072.C020809.packed 128 cuts20809 = true := by
 decide +kernel
def pointBounds20809 : List (Nat × Nat × Nat) := [(2731414528,100534215073108,100534595742778),(2731500544,100534629331460,100535010001369)]
theorem point_links_checked20809 : (cuts20809.take 2).map (fun c => (2731409409-1+2*2^9*c.k,100534189310343+c.lower,100534569979998+c.upper)) = pointBounds20809 := by
 decide +kernel
def cuts20810 : List PrefixCut := [⟨45,213716030,213716155⟩,
⟨128,616304537,616304895⟩]
theorem checked20810 : checkPrefixCuts (2^48) 2731540481 9 Manual.Count131072.C020810.packed 128 cuts20810 = true := by
 decide +kernel
def pointBounds20810 : List (Nat × Nat × Nat) := [(2731586560,100535029768577,100535410438726)]
theorem point_links_checked20810 : (cuts20810.take 1).map (fun c => (2731540481-1+2*2^9*c.k,100534816052547+c.lower,100535196722571+c.upper)) = pointBounds20810 := by
 decide +kernel
def cuts20811 : List PrefixCut := [⟨1,4430774,4430776⟩,
⟨85,418650031,418650271⟩,
⟨128,630288345,630288708⟩]
theorem checked20811 : checkPrefixCuts (2^48) 2731671553 9 Manual.Count131072.C020811.packed 128 cuts20811 = true := by
 decide +kernel
def pointBounds20811 : List (Nat × Nat × Nat) := [(2731672576,100535436787858,100535817458242),(2731758592,100535851007115,100536231677737)]
theorem point_links_checked20811 : (cuts20811.take 2).map (fun c => (2731671553-1+2*2^9*c.k,100535432357084+c.lower,100535813027466+c.upper)) = pointBounds20811 := by
 decide +kernel
def cuts20812 : List PrefixCut := [⟨41,194840197,194840311⟩,
⟨125,607075718,607076073⟩,
⟨128,620778899,620779261⟩]
theorem checked20812 : checkPrefixCuts (2^48) 2731802625 9 Manual.Count131072.C020812.packed 128 cuts20812 = true := by
 decide +kernel
def pointBounds20812 : List (Nat × Nat × Nat) := [(2731844608,100536257485626,100536638156485),(2731930624,100536669721147,100537050392247)]
theorem point_links_checked20812 : (cuts20812.take 2).map (fun c => (2731802625-1+2*2^9*c.k,100536062645429+c.lower,100536443316174+c.upper)) = pointBounds20812 := by
 decide +kernel
def cuts20813 : List PrefixCut := [⟨81,393779907,393780140⟩,
⟨128,623221811,623222176⟩]
theorem checked20813 : checkPrefixCuts (2^48) 2731933697 9 Manual.Count131072.C020813.packed 128 cuts20813 = true := by
 decide +kernel
def pointBounds20813 : List (Nat × Nat × Nat) := [(2732016640,100537077204235,100537457875575)]
theorem point_links_checked20813 : (cuts20813.take 1).map (fun c => (2731933697-1+2*2^9*c.k,100536683424328+c.lower,100537064095435+c.upper)) = pointBounds20813 := by
 decide +kernel
def cuts20814 : List PrefixCut := [⟨37,181943437,181943543⟩,
⟨121,591358411,591358752⟩,
⟨128,625664613,625664975⟩]
theorem checked20814 : checkPrefixCuts (2^48) 2732064769 9 Manual.Count131072.C020814.packed 128 cuts20814 = true := by
 decide +kernel
def pointBounds20814 : List (Nat × Nat × Nat) := [(2732102656,100537488589576,100537869261154),(2732188672,100537898004550,100538278676363)]
theorem point_links_checked20814 : (cuts20814.take 2).map (fun c => (2732064769-1+2*2^9*c.k,100537306646139+c.lower,100537687317611+c.upper)) = pointBounds20814 := by
 decide +kernel
def cuts20815 : List PrefixCut := [⟨77,373344548,373344767⟩,
⟨128,622028871,622029231⟩]
theorem checked20815 : checkPrefixCuts (2^48) 2732195841 9 Manual.Count131072.C020815.packed 128 cuts20815 = true := by
 decide +kernel
def pointBounds20815 : List (Nat × Nat × Nat) := [(2732274688,100538305655300,100538686327353)]
theorem point_links_checked20815 : (cuts20815.take 1).map (fun c => (2732195841-1+2*2^9*c.k,100537932310752+c.lower,100538312982586+c.upper)) = pointBounds20815 := by
 decide +kernel
def cuts20816 : List PrefixCut := [⟨33,156481181,156481273⟩,
⟨117,563694171,563694497⟩,
⟨128,615509119,615509476⟩]
theorem checked20816 : checkPrefixCuts (2^48) 2732326913 9 Manual.Count131072.C020816.packed 128 cuts20816 = true := by
 decide +kernel
def pointBounds20816 : List (Nat × Nat × Nat) := [(2732360704,100538710820804,100539091493090),(2732446720,100539118033794,100539498706314)]
theorem point_links_checked20816 : (cuts20816.take 2).map (fun c => (2732326913-1+2*2^9*c.k,100538554339623+c.lower,100538935011817+c.upper)) = pointBounds20816 := by
 decide +kernel
def cuts20817 : List PrefixCut := [⟨73,354767191,354767396⟩,
⟨128,622175308,622175671⟩]
theorem checked20817 : checkPrefixCuts (2^48) 2732457985 9 Manual.Count131072.C020817.packed 128 cuts20817 = true := by
 decide +kernel
def pointBounds20817 : List (Nat × Nat × Nat) := [(2732532736,100539524615933,100539905288689)]
theorem point_links_checked20817 : (cuts20817.take 1).map (fun c => (2732457985-1+2*2^9*c.k,100539169848742+c.lower,100539550521293+c.upper)) = pointBounds20817 := by
 decide +kernel
def cuts20818 : List PrefixCut := [⟨29,139161259,139161338⟩,
⟨113,552722065,552722384⟩,
⟨128,622969437,622969797⟩]
theorem checked20818 : checkPrefixCuts (2^48) 2732589057 9 Manual.Count131072.C020818.packed 128 cuts20818 = true := by
 decide +kernel
def pointBounds20818 : List (Nat × Nat × Nat) := [(2732618752,100539931185309,100540311858302),(2732704768,100540344746115,100540725419348)]
theorem point_links_checked20818 : (cuts20818.take 2).map (fun c => (2732589057-1+2*2^9*c.k,100539792024050+c.lower,100540172696964+c.upper)) = pointBounds20818 := by
 decide +kernel
def cuts20819 : List PrefixCut := [⟨69,335060332,335060522⟩,
⟨128,621600535,621600892⟩]
theorem checked20819 : checkPrefixCuts (2^48) 2732720129 9 Manual.Count131072.C020819.packed 128 cuts20819 = true := by
 decide +kernel
def pointBounds20819 : List (Nat × Nat × Nat) := [(2732790784,100540750053819,100541130727283)]
theorem point_links_checked20819 : (cuts20819.take 1).map (fun c => (2732720129-1+2*2^9*c.k,100540414993487+c.lower,100540795666761+c.upper)) = pointBounds20819 := by
 decide +kernel
def cuts20820 : List PrefixCut := [⟨25,118651749,118651817⟩,
⟨109,523521931,523522232⟩,
⟨128,615596964,615597320⟩]
theorem checked20820 : checkPrefixCuts (2^48) 2732851201 9 Manual.Count131072.C020820.packed 128 cuts20820 = true := by
 decide +kernel
def pointBounds20820 : List (Nat × Nat × Nat) := [(2732876800,100541155245771,100541535919470),(2732962816,100541560115953,100541940789885)]
theorem point_links_checked20820 : (cuts20820.take 2).map (fun c => (2732851201-1+2*2^9*c.k,100541036594022+c.lower,100541417267653+c.upper)) = pointBounds20820 := by
 decide +kernel
def cuts20821 : List PrefixCut := [⟨65,311649505,311649684⟩,
⟨128,615567411,615567769⟩]
theorem checked20821 : checkPrefixCuts (2^48) 2732982273 9 Manual.Count131072.C020821.packed 128 cuts20821 = true := by
 decide +kernel
def pointBounds20821 : List (Nat × Nat × Nat) := [(2733048832,100541963840491,100542344514657)]
theorem point_links_checked20821 : (cuts20821.take 1).map (fun c => (2732982273-1+2*2^9*c.k,100541652190986+c.lower,100542032864973+c.upper)) = pointBounds20821 := by
 decide +kernel
def cuts20822 : List PrefixCut := [⟨21,99278981,99279038⟩,
⟨105,502978239,502978530⟩,
⟨128,613993281,613993637⟩]
theorem checked20822 : checkPrefixCuts (2^48) 2733113345 9 Manual.Count131072.C020822.packed 128 cuts20822 = true := by
 decide +kernel
def pointBounds20822 : List (Nat × Nat × Nat) := [(2733134848,100542367037378,100542747711780),(2733220864,100542770736636,100543151411272)]
theorem point_links_checked20822 : (cuts20822.take 2).map (fun c => (2733113345-1+2*2^9*c.k,100542267758397+c.lower,100542648432742+c.upper)) = pointBounds20822 := by
 decide +kernel
def cuts20823 : List PrefixCut := [⟨61,292362505,292362679⟩,
⟨128,621172285,621172655⟩]
theorem checked20823 : checkPrefixCuts (2^48) 2733244417 9 Manual.Count131072.C020823.packed 128 cuts20823 = true := by
 decide +kernel
def pointBounds20823 : List (Nat × Nat × Nat) := [(2733306880,100543174114183,100543554789058)]
theorem point_links_checked20823 : (cuts20823.take 1).map (fun c => (2733244417-1+2*2^9*c.k,100542881751678+c.lower,100543262426379+c.upper)) = pointBounds20823 := by
 decide +kernel
def cuts20824 : List PrefixCut := [⟨17,83823036,83823086⟩,
⟨101,493971470,493971761⟩,
⟨128,626600205,626600569⟩]
theorem checked20824 : checkPrefixCuts (2^48) 2733375489 9 Manual.Count131072.C020824.packed 128 cuts20824 = true := by
 decide +kernel
def pointBounds20824 : List (Nat × Nat × Nat) := [(2733392896,100543586746999,100543967422120),(2733478912,100543996895433,100544377570795)]
theorem point_links_checked20824 : (cuts20824.take 2).map (fun c => (2733375489-1+2*2^9*c.k,100543502923963+c.lower,100543883599034+c.upper)) = pointBounds20824 := by
 decide +kernel
def cuts20825 : List PrefixCut := [⟨57,278433575,278433735⟩,
⟨128,627599828,627600191⟩]
theorem checked20825 : checkPrefixCuts (2^48) 2733506561 9 Manual.Count131072.C020825.packed 128 cuts20825 = true := by
 decide +kernel
def pointBounds20825 : List (Nat × Nat × Nat) := [(2733564928,100544407957743,100544788633338)]
theorem point_links_checked20825 : (cuts20825.take 1).map (fun c => (2733506561-1+2*2^9*c.k,100544129524168+c.lower,100544510199603+c.upper)) = pointBounds20825 := by
 decide +kernel
def cuts20826 : List PrefixCut := [⟨13,64766182,64766219⟩,
⟨97,469212824,469213097⟩,
⟨128,623657064,623657428⟩]
theorem checked20826 : checkPrefixCuts (2^48) 2733637633 9 Manual.Count131072.C020826.packed 128 cuts20826 = true := by
 decide +kernel
def pointBounds20826 : List (Nat × Nat × Nat) := [(2733650944,100544821890178,100545202566013),(2733736960,100545226336820,100545607012891)]
theorem point_links_checked20826 : (cuts20826.take 2).map (fun c => (2733637633-1+2*2^9*c.k,100544757123996+c.lower,100545137799794+c.upper)) = pointBounds20826 := by
 decide +kernel
def cuts20827 : List PrefixCut := [⟨53,252666791,252666945⟩,
⟨128,614257869,614258235⟩]
theorem checked20827 : checkPrefixCuts (2^48) 2733768705 9 Manual.Count131072.C020827.packed 128 cuts20827 = true := by
 decide +kernel
def pointBounds20827 : List (Nat × Nat × Nat) := [(2733822976,100545633447851,100546014124167)]
theorem point_links_checked20827 : (cuts20827.take 1).map (fun c => (2733768705-1+2*2^9*c.k,100545380781060+c.lower,100545761457222+c.upper)) = pointBounds20827 := by
 decide +kernel
def cuts20828 : List PrefixCut := [⟨9,44374514,44374538⟩,
⟨93,455681002,455681268⟩,
⟨128,622361943,622362307⟩]
theorem checked20828 : checkPrefixCuts (2^48) 2733899777 9 Manual.Count131072.C020828.packed 128 cuts20828 = true := by
 decide +kernel
def pointBounds20828 : List (Nat × Nat × Nat) := [(2733908992,100546039413443,100546420089995),(2733995008,100546450719931,100546831396725)]
theorem point_links_checked20828 : (cuts20828.take 2).map (fun c => (2733899777-1+2*2^9*c.k,100545995038929+c.lower,100546375715457+c.upper)) = pointBounds20828 := by
 decide +kernel
def cuts20829 : List PrefixCut := [⟨49,238126623,238126769⟩,
⟨128,615434497,615434866⟩]
theorem checked20829 : checkPrefixCuts (2^48) 2734030849 9 Manual.Count131072.C020829.packed 128 cuts20829 = true := by
 decide +kernel
def pointBounds20829 : List (Nat × Nat × Nat) := [(2734081024,100546855527495,100547236204533)]
theorem point_links_checked20829 : (cuts20829.take 1).map (fun c => (2734030849-1+2*2^9*c.k,100546617400872+c.lower,100546998077764+c.upper)) = pointBounds20829 := by
 decide +kernel
def cuts20830 : List PrefixCut := [⟨5,27178090,27178106⟩,
⟨89,433298384,433298633⟩,
⟨128,624875719,624876081⟩]
theorem checked20830 : checkPrefixCuts (2^48) 2734161921 9 Manual.Count131072.C020830.packed 128 cuts20830 = true := by
 decide +kernel
def pointBounds20830 : List (Nat × Nat × Nat) := [(2734167040,100547260013459,100547640690736),(2734253056,100547666133753,100548046811263)]
theorem point_links_checked20830 : (cuts20830.take 2).map (fun c => (2734161921-1+2*2^9*c.k,100547232835369+c.lower,100547613512630+c.upper)) = pointBounds20830 := by
 decide +kernel
def cuts20831 : List PrefixCut := [⟨45,219059728,219059855⟩,
⟨128,624228211,624228573⟩]
theorem checked20831 : checkPrefixCuts (2^48) 2734292993 9 Manual.Count131072.C020831.packed 128 cuts20831 = true := by
 decide +kernel
def pointBounds20831 : List (Nat × Nat × Nat) := [(2734339072,100548076770816,100548457448566)]
theorem point_links_checked20831 : (cuts20831.take 1).map (fun c => (2734292993-1+2*2^9*c.k,100547857711088+c.lower,100548238388711+c.upper)) = pointBounds20831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000025
