import PlattPointSubsetKernel
import PlattPointPackets.S6B000156
import PlattPointPackets.S6B000157
import PlattPointPackets.S6B000158
import PlattPointPackets.S6B000159
import PlattPointPackets.S6B000160
import PlattPointPackets.S6B000161
import PlattPointPackets.S6B000162
import PlattPointPackets.S6B000163
import PlattPointPackets.S6B000164
import PlattPointPackets.S6B000165
import PlattPointPackets.S6B000166
import PlattPointPackets.S6B000167
import PlattPointPackets.S6B000168
import PlattPointPackets.S6B000169
import PlattPointPackets.S6B000170
import PlattGlobalGrid.S8B000076
namespace ChenEffective.PlattWindow.PointCovers.S8B000076
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000156.points ++ ChenEffective.PlattWindow.PointPackets.S6B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000160.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000170.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000076.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000076.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000076
