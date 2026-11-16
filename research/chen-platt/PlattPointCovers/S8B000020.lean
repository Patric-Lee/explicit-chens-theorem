import PlattPointSubsetKernel
import PlattPointPackets.S4B000157
import PlattPointPackets.S4B000158
import PlattPointPackets.S4B000159
import PlattPointPackets.S4B000160
import PlattPointPackets.S4B000161
import PlattPointPackets.S4B000162
import PlattPointPackets.S4B000163
import PlattPointPackets.S4B000164
import PlattPointPackets.S4B000165
import PlattPointPackets.S4B000166
import PlattGlobalGrid.S8B000020
namespace ChenEffective.PlattWindow.PointCovers.S8B000020
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000157.points ++ ChenEffective.PlattWindow.PointPackets.S4B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000160.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000166.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000020.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000020.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000020
