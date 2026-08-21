import unittest

from server import validation
from server.tests.testutil import sample_table, sample_profile


class TableValidationTests(unittest.TestCase):
    def test_valid_table_passes(self):
        validation.validate_table(sample_table())  # must not raise

    def test_wrong_row_count_rejected(self):
        table = sample_table()[:-1]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_wrong_col_count_rejected(self):
        table = sample_table()
        table[3] = [0.0, 0.0, 0.0]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_nonzero_row_zero_rejected(self):
        table = sample_table()
        table[0] = [0.0, 0.0, 0.0, 1.0]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_out_of_range_value_rejected(self):
        table = sample_table()
        table[5] = [4.1, 0.0, 0.0, 0.0]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_boundary_values_accepted(self):
        table = sample_table()
        table[5] = [4.0, -4.0, 0.0, 0.0]
        validation.validate_table(table)  # must not raise

    def test_non_numeric_entry_rejected(self):
        table = sample_table()
        table[5] = ["x", 0.0, 0.0, 0.0]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_bool_entry_rejected(self):
        table = sample_table()
        table[5] = [True, 0.0, 0.0, 0.0]
        with self.assertRaises(validation.ValidationError):
            validation.validate_table(table)

    def test_not_a_list_rejected(self):
        with self.assertRaises(validation.ValidationError):
            validation.validate_table({"not": "a table"})


class ProfileValidationTests(unittest.TestCase):
    def test_valid_profile_passes(self):
        validation.validate_profile(sample_profile())  # must not raise

    def test_period_out_of_range_rejected(self):
        for bad_period in (0, 9, -1):
            with self.subTest(period=bad_period):
                profile = {"period": bad_period, "hazards": [[0, 0, 0, 0]] * max(bad_period, 1)}
                with self.assertRaises(validation.ValidationError):
                    validation.validate_profile(profile)

    def test_hazards_row_count_must_match_period(self):
        profile = {"period": 2, "hazards": [[0.1, 0.1, 0.1, 0.1]]}
        with self.assertRaises(validation.ValidationError):
            validation.validate_profile(profile)

    def test_hazard_out_of_range_rejected(self):
        profile = {"period": 1, "hazards": [[1.5, 0.0, 0.0, 0.0]]}
        with self.assertRaises(validation.ValidationError):
            validation.validate_profile(profile)

    def test_hazard_boundary_accepted(self):
        profile = {"period": 1, "hazards": [[0.0, 1.0, 0.0, 1.0]]}
        validation.validate_profile(profile)  # must not raise

    def test_max_period_accepted(self):
        profile = {"period": 8, "hazards": [[0.1, 0.1, 0.1, 0.1]] * 8}
        validation.validate_profile(profile)  # must not raise

    def test_not_an_object_rejected(self):
        with self.assertRaises(validation.ValidationError):
            validation.validate_profile([1, 2, 3])


class AttackLevelValidationTests(unittest.TestCase):
    def test_valid_levels_accepted(self):
        for level in validation.ATTACK_LEVELS:
            validation.validate_attack_level(level)  # must not raise

    def test_invalid_level_rejected(self):
        with self.assertRaises(validation.ValidationError):
            validation.validate_attack_level("ultra")

    def test_deep_rejected_for_batch(self):
        with self.assertRaises(validation.ValidationError):
            validation.validate_attack_level("deep", allowed=validation.BATCH_LEVELS)


if __name__ == "__main__":
    unittest.main()
