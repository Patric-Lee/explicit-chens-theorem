import PlattPointSubsetKernel
import PlattPointPackets.S2B000188
import PlattPointPackets.S2B000189
import PlattPointPackets.S2B000190
import PlattPointPackets.S2B000191
import PlattPointPackets.S2B000192
import PlattGlobalGrid.S7B000040
namespace ChenEffective.PlattWindow.PointCovers.S7B000040
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000188.points ++ ChenEffective.PlattWindow.PointPackets.S2B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000192.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000040.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000040.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000040
