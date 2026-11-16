import PlattPointSubsetKernel
import PlattPointPackets.S5B000155
import PlattPointPackets.S5B000156
import PlattPointPackets.S5B000157
import PlattPointPackets.S5B000158
import PlattPointPackets.S5B000159
import PlattPointPackets.S5B000160
import PlattPointPackets.S5B000161
import PlattPointPackets.S5B000162
import PlattPointPackets.S5B000163
import PlattPointPackets.S5B000164
import PlattPointPackets.S5B000165
import PlattPointPackets.S5B000166
import PlattPointPackets.S5B000167
import PlattGlobalGrid.S8B000051
namespace ChenEffective.PlattWindow.PointCovers.S8B000051
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000155.points ++ ChenEffective.PlattWindow.PointPackets.S5B000156.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000160.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000167.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000051.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000051.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000051
